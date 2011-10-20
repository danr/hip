{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns #-}
module Language.HFOL.ToTPTP where

import Language.HFOL.Core
import Language.HFOL.FixBranches
import Language.HFOL.Pretty
import Language.HFOL.ToTPTPMonad
import qualified Language.TPTP as T

import Control.Arrow ((&&&))
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

preludeEnv :: Env
preludeEnv = flip (foldr addCons) datatypes
           $ emptyEnv
  where
    datatypes :: [[(Name,Int)]]
    datatypes = [ [("Tup" ++ show x,x)] | x <- [0..4] ] ++
                [ [("Cons",2),("Nil",0)]
                , [("True",0),("False",0)]
                , [("Nothing",0),("Just",1)]
                , [("Zero",0),("Succ",1)]
                , [(".Bottom",0)]
                ]

toTPTP :: [Decl] -> [T.Decl]
toTPTP ds = envStDecls env st ++ axioms
  where
    funs = map (funcName &&& length . funcArgs) ds
    env = addFuns funs preludeEnv
    (axioms,st) = runTPTP env (concat <$> mapM translate ds)

-- Notice that this function works well on an empty argument list
applyFun :: Name -> [T.Term] -> ToTPTP T.Term
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

translateExpr :: Expr -> ToTPTP T.Term
translateExpr (Var n) = applyFun n []
translateExpr e       = applyFun (exprName e) =<< mapM translateExpr (exprArgs e)

translatePattern :: Pattern -> ToTPTP T.Term
translatePattern (PVar n)    = applyFun n []
translatePattern (PCon c as) = applyFun c =<< mapM translatePattern as

forall :: [T.VarName] -> T.Formula -> T.Formula
forall [] phi = phi
forall xs phi = T.Forall xs phi

withPrevious :: [a] -> [(a,[a])]
withPrevious [] = []
withPrevious (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- withPrevious xs]

infix 4 ===
infixr 3 /\
infixr 2 \/
infixl 1 ==>
t1 === t2 = T.EqOp t1 (T.:==) t2
f1 ==> f2 = T.BinOp f1 (T.:=>) f2
f1 /\  f2 = T.BinOp f1 (T.:&) f2
f1 \/  f2 = T.BinOp f1 (T.:|) f2

translate :: Decl -> ToTPTP [T.Decl]
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


translateBranch :: T.Term             -- ^ The function term
                -> T.Term           -- ^ The case scrutinee term
                -> Pattern          -- ^ The current pattern
                -> Expr             -- ^ The current rhs expr of pattern
                -> [Pattern]        -- ^ The previous patterns
                -> ToTPTP T.Formula -- ^ The resulting declaration for this branch
translateBranch lhs t p e prev =
  let constraints :: [[(Name,Pattern)]]
      constraints = moreSpecificPatterns p prev
  in  bindPattern p $ \vars -> forall vars <$> do
          rhs <- translateExpr e
          p'  <- translatePattern p
          makeConstraints (t === p' ==> lhs === rhs) constraints

makeConstraints :: T.Formula -> [[(Name,Pattern)]] -> ToTPTP T.Formula
makeConstraints t css = foldr (\/) t <$> mapM makeConstraint css

makeConstraint :: [(Name,Pattern)] -> ToTPTP T.Formula
makeConstraint [] = error "empty constraint?!"
makeConstraint cs = foldr1 (/\) <$> mapM constraint cs

-- Note that this constraint is negated
constraint :: (Name,Pattern) -> ToTPTP T.Formula
constraint (n,p) = do
  QuantVar x <- lookupName n
  (T.Var x ===) <$> invertPattern p (T.Var x)

-- | Inverts a pattern into projections
--
-- > invertPattern (C (E a b) c) x =
-- >     C (E (projE1 (projC1 x)) (projE2 (projC1 x))) (projC2 x)
invertPattern :: Pattern -> T.Term -> ToTPTP (T.Term)
invertPattern (PVar _)      x = return x
invertPattern (PCon n pats) x = do
  projs <- lookupProj n
  ConVar c <- lookupName n
  T.Fun c <$> sequence
    (zipWith (\pat proj -> invertPattern pat (T.Fun proj [x])) pats projs)