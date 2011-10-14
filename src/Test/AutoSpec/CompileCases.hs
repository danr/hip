{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Test.AutoSpec.CompileCases where

import Test.AutoSpec.Core
import Control.Monad
import Control.Monad.State
import Control.Applicative
import Control.Arrow

-- Names in scope, variable supply. Scope is not yet used to generate
-- interesting variable names.
type St = ([Name],[Name])

newtype N a = N { runN :: State St a } 
  deriving (Functor,Applicative,Monad,MonadState St)

inScope :: N a -> N a
inScope m = do
  v <- gets fst
  x <- m
  modify (first (const v))
  return x

newVar :: N Name
newVar = do
  (v,x:xs) <- get
  put (v,xs)
  return x

compile :: ExtExpr -> N CoreExpr
compile (Let n e1 e2) = inScope $ liftM2 (Let n) (compile e1) (compile e2)
compile (Case n brs)  = match [n] (map (\(Branch p e) -> ([p],e)) brs) Fail
compile (App e1 e2)   = liftM2 App (compile e1) (compile e2)
compile (Cons n es)   = Cons n <$> mapM compile es
compile (Var x)       = return (Var x)                        
compile Fail          = return Fail

match :: [Name] -> [([ExtPattern],ExtExpr)] -> ExtExpr -> N CoreExpr
-- Empty rule
match [] (([],e):_) d = compile e
match [] []         d = compile d
-- Variable rule
match (u:us) pats d | all (varPat . head . fst) pats =
  let pats' = map (\(PVar v:ps,e) -> (ps,subst v u e)) pats
  in  match us pats' d
-- Constructor rule
match (u:us) pats d | all (conPat . head . fst) pats = do
  brs <- forM pats $ \(PCons c args:ps,e) -> do
                         vs <- mapM (const newVar) args
                         let args' = map denest args
                         e' <- match (vs ++ us) [(args' ++ ps,e)] d
                         return (Branch (PCons c vs) e')
  return (Case u brs)

demo :: CoreExpr
demo = evalState (runN m) ([],["_" ++ show x | x <- [0..]])
 where
  m = match ["u1","u2","u3"]
            [([PVar "f",PCons "Nil" []                             ,PVar "ys"                                  ],Cons "A" (map Var ["f","ys"]))
            ,([PVar "f",PCons "Cons" [NP (PVar "x"),NP (PVar "xs")],PVar "ys"                                  ],Cons "B" (map Var ["f","x","xs"]))
            ,([PVar "f",PCons "Cons" [NP (PVar "x"),NP (PVar "xs")],PCons "Cons" [NP (PVar "y"),NP (PVar "ys")]],Cons "C" (map Var ["f","x","xs","y","ys"]))
            ]
            Fail
