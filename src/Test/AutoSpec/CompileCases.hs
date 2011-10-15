{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Test.AutoSpec.CompileCases where

import Test.AutoSpec.Core
import Control.Monad
import Control.Monad.State
import Control.Applicative
import Control.Arrow
import Data.Set hiding (map,filter)

-- Names in scope
type St = Set Name

newtype N a = N { runN :: State St a } 
  deriving (Functor,Applicative,Monad,MonadState St)

inNewScope :: [Name] -> N a -> N a
inNewScope ns m = do
  s <- get
  modify (\s -> foldl (flip insert) s ns)
  r <- m
  put s
  return r

newVar :: Name -> N Name
newVar n = do
  let ns = n : [ n ++ show x | x <- [0..] ]
  s <- get
  return $ head $ filter (`notMember` s) ns


compile :: ExtExpr -> N CoreExpr
compile (Case n brs)  = inNewScope [n] $ match [n] (map (\(Branch p e) -> ([p],e)) brs) Fail
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
                         let suggest (NP (PVar v)) = v
                             suggest _             = "_"
                         vs <- mapM (newVar . suggest) args
                         let args' = map denest args
                         e' <- inNewScope vs $ match (vs ++ us) [(args' ++ ps,e)] d
                         return (Branch (PCons c vs) e')
  return (Case u brs)

demo :: CoreExpr
demo = evalState (runN m) (fromList ["u1","u2","u3"])
 where
  m = match ["u1","u2","u3"]
            [([PVar "f",PCons "Nil" []                             ,PVar "ys"                                  ],Cons "A" (map Var ["f","ys"]))
            ,([PVar "f",PCons "Cons" [NP (PVar "x"),NP (PVar "xs")],PVar "ys"                                  ],Cons "B" (map Var ["f","x","xs"]))
            ,([PVar "f",PCons "Cons" [NP (PVar "x"),NP (PVar "xs")],PCons "Cons" [NP (PVar "y"),NP (PVar "ys")]],Cons "C" (map Var ["f","x","xs","y","ys"]))
            ]
            Fail
