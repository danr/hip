{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Test.AutoSpec.CompileCases where

import Test.AutoSpec.Core
import Test.AutoSpec.Pretty
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Applicative hiding (empty)
import Control.Arrow
import Data.List hiding (insert)
import Data.Function 
import Data.Maybe
import Data.Ord
import Data.Set hiding (map,filter)

-- Names in scope
type St = Set Name

newtype N a = N { runN :: WriterT [String] (State St) a }
  deriving (Functor,Applicative,Monad,MonadState St,MonadWriter [String])

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

compileProg :: [ExtDecl] -> ([CoreDecl],[String])
compileProg ds = flip evalState empty $ runWriterT $ runN $ do
  let ds' = sortGroupOn funName ds
  mapM compileFun ds'

suggest (NP (PVar v)) = Just v
suggest _             = Nothing

makeCasevars = mapM ((\n -> inNewScope [n] (newVar n))
                    . fromMaybe "u" . msum . map suggest)

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

sortGroupOn :: Ord b => (a -> b) -> [a] -> [[a]]
sortGroupOn f = groupBy (((== EQ) .) . (compare  `on` f)) . sortBy (comparing f)

data Equation = [ExtPattern] := ExtExpr
  deriving (Show,Eq,Ord)

infix 4 :=              
infix 8 &
     
(f & g) x = f x := g x            
              
rhs :: Equation -> [ExtPattern]
rhs (r := _) = r

lhs :: Equation -> ExtExpr
lhs (_ := l) = l

rhsHead :: Equation -> ExtPattern
rhsHead = head . rhs

write = tell . return

prettyEq (ps := e) = "[" ++ intercalate " , " (map prettyCore ps) ++ "]"
                     ++ " := " ++ prettyCore e

writeMatch ns eqs d = do
  write ("match\t" ++ "[" ++ intercalate " , " ns ++ "]")
  mapM_ (\e -> write $ "\t" ++ prettyEq e) (eqs)
  write ("\t" ++ prettyCore d)

match :: [Name] -> [Equation] -> CoreExpr -> N CoreExpr
-- Empty rule
match [] pats d = do
  writeMatch [] pats d
  write "Empty rule\n"
  foldr (:|) d <$> mapM compile [ e | [] := e <- pats ]
-- Variable rule
match (u:us) pats d | all (varPat . rhsHead) pats = do
  writeMatch (u:us) pats d
  write "Variable rule\n"
  let pats' = map (\(PVar v:ps := e) -> ps := subst v u e) pats
  match us pats' d
-- Constructor rule
match (u:us) pats d | all (conPat . rhsHead) pats = do
  writeMatch (u:us) pats d
  write "Constructor rule\n"
  let groups = sortGroupOn (patName . rhsHead) pats
  brs <- forM groups $ \grp -> do
             let matrix = transpose (map (patArgs . rhsHead) grp)
             vs <- makeCasevars matrix
             let prependArgs (PCons _ args:ps := e) = map denest args ++ ps := e
             e' <- inNewScope vs $ match (vs ++ us) (map prependArgs grp) d
             let c = patName (rhsHead (head grp))
             return (Branch (PCons c vs) e')
  return (Case u brs)
-- Mixture rule
match us pats d = do
  writeMatch us pats d
  write "Mixture rule\n"
  go pats d
 where
  go (p:ps) d = do d' <- go ps d
                   write "From mixture rule:"
                   match us [p] d'
  go []     d = match us [] d

--            foldr (\p d' -> match us p d') d pats

-- Constructor rule will only preserve semantics of casing if the
-- sorting is stable, and it is documented that Data.List.sortBy is:
-- http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#sort
