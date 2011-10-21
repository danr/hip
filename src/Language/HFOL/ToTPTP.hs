{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns #-}
module Language.HFOL.ToTPTP where

import Language.HFOL.Core
import Language.HFOL.FixBranches
import Language.HFOL.Pretty
import Language.HFOL.Monad
import Language.TPTP hiding (Decl,Var)
import qualified Language.TPTP as T

import Control.Arrow ((&&&))
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

import Data.Maybe (catMaybes,isNothing)

datatypes :: [[(Name,Int)]]
datatypes = [ [("Tup" ++ show x,x)] | x <- [0..4] ] ++
            [ [("Cons",2),("Nil",0)]
            , [("True",0),("False",0)]
            , [("Nothing",0),("Just",1)]
            , [("Zero",0),("Succ",1)]
            , [(bottomName,0)]
            ]

toTPTP :: [Decl] -> [T.Decl]
toTPTP ds = runTM $ addFuns funs $ addCons datatypes $ do
               faxioms <- concat <$> mapM translate ds
               extra   <- envStDecls
               return $ extra ++ faxioms
  where
    funs = map (funcName &&& length . funcArgs) ds

-- Notice that this function works well on an empty argument list
applyFun :: Name -> [Term] -> TM Term
applyFun n as = do
  b <- lookupName n
  case b of
    QuantVar x          -> return (appFold (T.Var x) as)
    Indirection e       -> do t <- translateExpr e
                              return (appFold t as)
    b@(boundName -> fn) -> do
      arity <- lookupArity n
      if length as < arity
        then -- Partial application
          do useFunPtr n
             return $ appFold (T.Fun (makeFunPtrName fn) []) as
        else -- Function has enough arguments, and could possibly have more
          do -- (for functions returning functions)
             when (boundCon b && length as > arity) $ error $ "Internal error: "
                 ++ "constructor " ++ n ++ "applied to too many arguments."
             return $ appFold (T.Fun fn (take arity as)) (drop arity as)

translateExpr :: Expr -> TM Term
translateExpr (Var n) = applyFun n []
translateExpr e       = applyFun (exprName e) =<< mapM translateExpr (exprArgs e)

translatePattern :: Pattern -> TM Term
translatePattern (PVar n)    = applyFun n []
translatePattern (PCon c as) = applyFun c =<< mapM translatePattern as

withPrevious :: [a] -> [(a,[a])]
withPrevious [] = []
withPrevious (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- withPrevious xs]

translate :: Decl -> TM [T.Decl]
translate (Func fname args (Expr e)) = bindNames args $ \vars -> do
    rhs <- applyFun fname (map T.Var vars)
    lhs <- translateExpr e
    return [T.Axiom (fname ++ "axiom") $ forall vars $ rhs === lhs]
translate (Func fname args (Case scrutinee brs)) = catMaybes <$> sequence
    [ locally (translateBranch p e (map brPat prevbrs) num)
    | ((p :-> e,prevbrs),num) <- zip (withPrevious (fixBranches brs)) [0..]
    ]
  where
    translateBranch pattern expr prev num = do
      d <- scrutinee ~~ pattern
      case d of
        Nothing -> return Nothing
        Just conds -> do
          lhs <- translateExpr (App fname (map Var args))
          rhs <- translateExpr expr
          formula <- (lhs === rhs) `withConditions` conds
          formula' <- formula `withConstraints` (moreSpecificPatterns pattern prev)
          qs <- popQuantified
          return $ Just $ T.Axiom (fname ++ "axiom" ++ show num)
                                  (forall qs formula')


type Condition = (Expr,Pattern)

-- Unify the scrutinee expression with the pattern,
-- returning just the conditions for this branch,
-- or nothing if this branch is unreachable
(~~) :: Expr -> Pattern -> TM (Maybe [Condition])
Con c as ~~ PCon c' ps | c == c'   = concatMaybe <$> zipWithM (~~) as ps
                       | otherwise = return Nothing
e        ~~ PVar n     = addIndirection n e >> noConditions
Var n    ~~ p          = addIndirection n (toExpr p) >> noConditions
App f as ~~ PCon c ps  = return $ return $ return (App f as,PCon c ps)

noConditions :: TM (Maybe [Condition])
noConditions = return (return [])

concatMaybe :: [Maybe [a]] -> Maybe [a]
concatMaybe ms | any isNothing ms = Nothing
               | otherwise        = Just (concat (catMaybes ms))

withConditions :: Formula -> [Condition] -> TM Formula
withConditions phi []    = return phi
withConditions phi conds = do
  conds' <- mapM translateCond conds
  return $ foldr1 (/\) conds' ==> phi

translateCond :: Condition -> TM Formula
translateCond (expr,pat) = liftM2 (===) (translateExpr expr)
                                        (translateExpr (toExpr pat))

type Constraint = (Name,Pattern)

withConstraints :: Formula -> [[Constraint]] -> TM Formula
withConstraints t css = foldl (\/) t <$> mapM conj css
  where
    conj :: [Constraint] -> TM Formula
    conj [] = error "empty constraint?!"
    conj cs = foldl1 (/\) <$> mapM disj cs

    disj :: Constraint -> TM Formula
    disj (n,p) = do
        b <- lookupName n
        x <- case b of
                 QuantVar x -> return x
                 _          -> error $ "disj : " ++ n ++ "," ++ show p ++ "," ++ show b
        (T.Var x ===) <$> invertPattern p (T.Var x)

-- | Inverts a pattern into projections
--
-- > invertPattern (C (E a b) c) x =
-- >     C (E (projE1 (projC1 x)) (projE2 (projC1 x))) (projC2 x)
invertPattern :: Pattern -> Term -> TM (Term)
invertPattern (PVar _)      x = return x
invertPattern (PCon n pats) x = do
  projs <- lookupProj n
  ConVar c <- lookupName n
  T.Fun c <$> sequence
    (zipWith (\pat proj -> invertPattern pat (T.Fun proj [x])) pats projs)