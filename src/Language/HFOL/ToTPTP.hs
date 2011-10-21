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
translate (Func fn args (Expr e)) = bindNames args $ \vars -> do
    rhs <- applyFun fn (map T.Var vars)
    lhs <- translateExpr e
    return [T.Axiom (fn ++ "axiom") $ forall vars $ rhs === lhs]
translate (Func fn args (Case ec brs)) = bindNames args $ \vars -> do
    t <- translateExpr ec
    lhs <- applyFun fn (map T.Var vars)
    sequence
       [ (T.Axiom (fn ++ "axiom") . forall vars) <$>
            translateBranch lhs t p e (map brPat pbrs)
       | (p :-> e,pbrs) <- withPrevious (fixBranches brs)
       ]

translateBranch :: Term           -- ^ The function term
                -> Term           -- ^ The case scrutinee term
                -> Pattern          -- ^ The current pattern
                -> Expr             -- ^ The current rhs expr of pattern
                -> [Pattern]        -- ^ The previous patterns
                -> TM Formula -- ^ The resulting declaration for this branch
translateBranch lhs t p e prev =
  let constraints :: [[(Name,Pattern)]]
      constraints = moreSpecificPatterns p prev
  in  bindPattern p $ \vars -> forall vars <$> do
          rhs <- translateExpr e
          p'  <- translatePattern p
          makeConstraints (t === p' ==> lhs === rhs) constraints

makeConstraints :: Formula -> [[(Name,Pattern)]] -> TM Formula
makeConstraints t css = foldl (\/) t <$> mapM makeConstraint css

makeConstraint :: [(Name,Pattern)] -> TM Formula
makeConstraint [] = error "empty constraint?!"
makeConstraint cs = foldl1 (/\) <$> mapM constraint cs

constraint :: (Name,Pattern) -> TM Formula
constraint (n,p) = do
  QuantVar x <- lookupName n
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