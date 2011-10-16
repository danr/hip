{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Test.AutoSpec.CompileCases where

import Test.AutoSpec.Core
import Control.Monad
import Control.Monad.State
import Control.Applicative hiding (empty)
import Control.Arrow
import Data.List hiding (insert)
import Data.Function 
import Data.Maybe
import Data.Ord
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

compileProg :: [ExtDecl] -> [CoreDecl]
compileProg ds = flip evalState empty $ runN $ do
  let ds' = groupSorted (\(Fun n _ _) -> n) ds
  mapM compileFun ds'

suggest (NP (PVar v)) = Just v
suggest _             = Nothing

makeCasevars = mapM ((\n -> inNewScope [n] (newVar n)) . fromMaybe "u" . msum . map suggest)

compileFun :: [ExtDecl] -> N CoreDecl
compileFun ds@(Fun n _ _:_) = do
  let matrix   = transpose (map funArgs ds)
  casevars <- makeCasevars matrix
  e <- inNewScope (n:casevars) $
           match casevars (map (map denest . funArgs & funExpr) ds) Fail
  return $ Fun n casevars e
  
compile :: ExtExpr -> N CoreExpr
compile (Case n brs)  = inNewScope [n] $
                            match [n] (map (\(Branch p e) -> [p] := e) brs) Fail
compile (App e1 e2)   = liftM2 App (compile e1) (compile e2)
compile (Cons n es)   = Cons n <$> mapM compile es
compile (Var x)       = return (Var x)                        
compile Fail          = return Fail

groupSorted :: Ord b => (a -> b) -> [a] -> [[a]]
groupSorted f = groupBy (((== EQ) .) . (compare  `on` f)) . sortBy (comparing f)

data Equation = [ExtPattern] := ExtExpr

infix 4 :=              
infix 8 &
     
(f & g) x = f x := g x            
              
rhs :: Equation -> [ExtPattern]
rhs (r := _) = r

lhs :: Equation -> ExtExpr
lhs (_ := l) = l

rhsHead :: Equation -> ExtPattern
rhsHead = head . rhs

match :: [Name] -> [Equation] -> ExtExpr -> N CoreExpr
-- Empty rule
match [] (([] := e):_) d = compile e
match [] []         d = compile d
-- Variable rule
match (u:us) pats d | all (varPat . rhsHead) pats =
  let pats' = map (\(PVar v:ps := e) -> ps := subst v u e) pats
  in  match us pats' d
-- Constructor rule
match (u:us) pats d | all (conPat . rhsHead) pats = do
  -- This will only preserve semantics of casing if the sorting is stable,
  -- and it is documented that Data.List.sortBy is:
  -- http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#sort
  let groups = groupSorted (patName . rhsHead) pats
  brs <- forM groups $ \grp -> do
             let matrix = transpose (map (patArgs . rhsHead) grp)
             vs <- makeCasevars matrix
             e' <- inNewScope vs $
                       match (vs ++ us)
                             (map (\(PCons _ args:ps := e) -> (map denest args ++ ps := e)) grp)
                             d
             let c = patName (rhsHead (head grp))
             return (Branch (PCons c vs) e')
  return (Case u brs)
-- TODO: Mix rule

{-
demo :: CoreExpr
demo = evalState (runN m) (fromList ["u1","u2","u3"])
 where
  m = match ["u1","u2","u3"]
            [([PVar "f",PCons "Nil" []                             ,PVar "ys"                                  ],Cons "A" (map Var ["f","ys"]))
            ,([PVar "f",PCons "Cons" [NP (PVar "x"),NP (PVar "xs")],PVar "ys"                                  ],Cons "B" (map Var ["f","x","xs"]))
            ,([PVar "f",PCons "Cons" [NP (PVar "x"),NP (PVar "xs")],PCons "Cons" [NP (PVar "y"),NP (PVar "ys")]],Cons "C" (map Var ["f","x","xs","y","ys"]))
            ]
            Fail
-}