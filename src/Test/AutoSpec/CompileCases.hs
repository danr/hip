{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts #-}
module Test.AutoSpec.CompileCases where

import Test.AutoSpec.Core
import Test.AutoSpec.Pretty
import Control.Monad
import Control.Monad.RWS
import Control.Applicative hiding (empty)
import Control.Arrow hiding ((|||))
import Data.List hiding (insert)
import Data.Function 
import Data.Maybe
import Data.Ord
import Data.Generics.Uniplate.Data
import Data.Data
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

-- Names in scope
type St = (Set Name)

                 -- constructors of each type, type of each constructor
type Datatypes = (Map Name [Name],Map Name Name)

addNewDatatype :: Name -> [Name] -> Datatypes -> Datatypes
addNewDatatype t cs (ctors,types) = (M.insert t cs ctors
                                    ,foldl (flip (`M.insert` t)) types cs
                                    )

emptyEnv :: Datatypes
emptyEnv = (M.empty,M.empty)

exampleDatatypes :: Datatypes
exampleDatatypes = addNewDatatype "Bool" ["True","False"]
                 $ addNewDatatype "List" ["Nil","Cons"]
                   emptyEnv

lookupType :: MonadReader Datatypes m => Name -> m Name
lookupType c = asks (fromMaybe (error ("constructor not registered" ++ c))
                    . M.lookup c . snd)
                   
lookupCtors :: MonadReader Datatypes m => Name -> m [Name]
lookupCtors t = asks (fromMaybe (error ("type not registered" ++ t))
                    . M.lookup t . fst)
                   
newtype N a = N { runN :: RWS Datatypes [String] St a }
  deriving (Functor,Applicative,Monad
           ,MonadState St,MonadWriter [String],MonadReader Datatypes)

subst :: (Show k,Data k) => Name -> Name -> Expr k -> N (Expr k)
subst xold xnew = transformM f
  where f (Var x)      | x == xold = return (Var xnew)
        f (Case x brs) | x == xold = liftM (Case xnew) (mapM substbr brs)
        f e            = return e

        substbr (Branch p e)
            | xold `elem` pv = return (Branch p e)
            | otherwise      = liftM (Branch p) $ do
                                  when (xnew `elem` pv) $
                                     write $ "Warning: subst " ++ xnew
                                             ++ " which is bound by "
                                             ++ show p ++ "->" ++ show e
                                  f e
          where pv = patternVars p

patternVars :: Data k => Pattern k -> [Name]
patternVars p = [ v | PVar v <- universe p ]

freeVars :: Data k => Expr k -> [Name]
freeVars e = [ v | Var v <- universe e ]
  
inNewScope :: [Name] -> N a -> N a
inNewScope ns m = do
  s <- get
  modify (\s -> foldl (flip S.insert) s ns)
  r <- m
  put s
  return r

newVar :: Name -> N Name
newVar n = do
  let ns = n : [ n ++ show x | x <- [0..] ]
  s <- get
  return $ head $ filter (`S.notMember` s) ns

compileProg :: [ExtDecl] -> ([CoreDecl],[String])
compileProg ds = (\m -> evalRWS m exampleDatatypes S.empty) $ runN $ do
  let ds' = sortGroupOn funName ds
  mapM compileFun ds'

suggest (NP (PVar v)) = Just v
suggest _             = Nothing

makeCasevars = mapM (newVar . fromMaybe "u" . msum . map suggest)

compileFun :: [ExtDecl] -> N CoreDecl
compileFun ds@(Fun n _ _:_) = do
  let matrix   = transpose (map funArgs ds)
  casevars <- makeCasevars matrix
  e <- inNewScope (n:casevars ++ concatMap (freeVars . funExpr) ds) $
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
  mapM_ (\e -> write $ '\t' : prettyEq e) eqs
  write ('\t' : prettyCore d)

(|||) :: CoreExpr -> CoreExpr -> CoreExpr
Fail ||| e    = e
e    ||| Fail = e
e1   ||| e2   = transform f e1
                 where f Fail = e2
                       f x    = x

mkCase :: Name -> [CoreBranch] -> N CoreExpr
mkCase n brs = do
  let ctors = map (patName . branchPat) brs
  t <- lookupType (head ctors)
  cs <- lookupCtors t
  write $ "Type : " ++ t ++ ", Constructors : " ++ show cs
  if S.fromList ctors == S.fromList cs
     then return (Case n brs)
     else do d <- newVar "d"
             return (Case n (brs ++ [Branch (PVar d) Fail]))

match :: [Name] -> [Equation] -> CoreExpr -> N CoreExpr
-- Empty rule
match [] pats d = do
  writeMatch [] pats d
  write "Empty rule\n"
  foldr1 (|||) . (++ [d]) <$> mapM compile [ e | [] := e <- pats ]
-- Variable rule
match (u:us) pats d | all (varPat . rhsHead) pats = do
  writeMatch (u:us) pats d
  write "Variable rule\n"
  pats' <- mapM (\(PVar v:ps := e) -> liftM (ps :=) (subst v u e)) pats
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
  r <- mkCase u brs 
  write "Return from constructor rule\n"
  return (r ||| d)
-- Mixture rule
match us pats d = do
  writeMatch us pats d
  write "Mixture rule\n"
  go pats d
 where
  go [p]    d' = match us [p] d'
  go (p:ps) d' = match us [p] =<< go ps d'


--            foldr (\p d' -> match us p d') d pats

-- Constructor rule will only preserve semantics of casing if the
-- sorting is stable, and it is documented that Data.List.sortBy is:
-- http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#sort
