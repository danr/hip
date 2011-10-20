{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.HFOL.ToTPTPMonad
       (ToTPTP
       ,runTPTP
       ,Env
       ,emptyEnv
       ,St
       ,Bound(..)
       ,boundCon
       ,lookupName
       ,lookupArity
       ,lookupProj
       ,bindNames
       ,bindPattern
       ,makeFunPtrName
       ,addFuns
       ,addCons
       ,useFunPtr
       ,appFold
       ,envStDecls
       ) where

import Language.HFOL.Core
import qualified Language.TPTP as T
import Language.TPTP
import Language.TPTP.Pretty

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

-- | The ToTPTP monad.
--
--   The reader and state capabilities are kept abstract
newtype ToTPTP a = TM { unToTPTP :: ReaderT Env (State St) a }
  deriving (Functor,Applicative,Monad)

-- | Runs a computation in an environment, with an empty state.
--   The computation's result is returned with the updated state.
runTPTP :: Env -> ToTPTP a -> (a,St)
runTPTP env m = runState (runReaderT (unToTPTP m) env) emptySt

data Env = Env { arities    :: Map Name Int
                 -- ^ Arity of functions and constructors
               , boundNames :: Map Name Bound
                 -- ^ TPTP name of functions and constructors and quantified variables
               , conProj    :: Map Name [Name]
                 -- ^ Projection functions for constructors
               , conFam     :: Map Name [Name]
                 -- ^ The other constructors for a given constructor
               , namesupply :: [VarName]
               }

data St = St { usedFunPtrs :: Set Name
               -- ^ Which functions we need to produce ptr conversions for
             }

data Bound = QuantVar { quantVar  :: VarName }
           | FunVar   { boundName :: FunName }
           | ConVar   { boundName :: FunName }

boundCon :: Bound -> Bool
boundCon (ConVar _) = True
boundCon _          = False

-- | The empty environment
emptyEnv :: Env
emptyEnv = Env M.empty M.empty M.empty M.empty [ T.VarName ('X' : show x) | x <- [0..] ]

-- | The empty state
emptySt :: St
emptySt = St S.empty

-- | Insert /n/ elements to a map of /m/ elements
--
--   /O(n * log(m+n))/
insertMany :: Ord k => [(k,v)] -> Map k v -> Map k v
insertMany kvs m = foldr (uncurry M.insert) m kvs

-- | Looks up if a name is a variable or a function/constructor
lookupName :: Name -> ToTPTP Bound
lookupName n = TM $ asks (fromMaybe (error $ "lookupName, unbound: " ++ n)
                        . M.lookup n . boundNames)

-- | Looks up an arity of a function or constructor
lookupArity :: Name -> ToTPTP Int
lookupArity n = TM $ asks (fromMaybe (error $ "lookupArity, unbound: " ++ n)
                          . M.lookup n . arities)

-- | Looks up the projections for a constructor
lookupProj :: Name -> ToTPTP [FunName]
lookupProj n = TM $ asks ( map FunName
                         . fromMaybe (error $ "lookupProj, unbound: " ++ n)
                         . M.lookup n . conProj)

-- | Binds the names to quantified variables inside the action
bindNames :: [Name] -> ([VarName] -> ToTPTP a) -> ToTPTP a
bindNames ns vm = TM $ do
    let n = length ns
    vs <- asks (take n . namesupply)
    let TM m = vm vs
    flip local m $ \e -> e
         { boundNames = insertMany (zipWith (\n v -> (n,QuantVar v)) ns vs)
                                   (boundNames e)
         , namesupply = drop n (namesupply e) }

-- | Bind all variables in a pattern
bindPattern :: Pattern -> ([VarName] -> ToTPTP a) -> ToTPTP a
bindPattern p m = bindNames (fv p) m
  where
    fv (PVar x)    = return x
    fv (PCon c xs) = concatMap fv xs

-- | Make a pointer name of a name
makePtrName :: Name -> Name
makePtrName n = n ++ "_ptr"

-- | Make a pointer of a function name
makeFunPtrName :: FunName -> FunName
makeFunPtrName = FunName . makePtrName . funName

-- | Bind names that are functions or constructors
bindFunVars :: [Name] -> (FunName -> Bound) -> Env -> Env
bindFunVars ns mk e = e
   { boundNames = insertMany [(n,mk (FunName n))| n <- ns] (boundNames e) }

addArities :: [(Name,Int)] -> Env -> Env
addArities funs e = e { arities = insertMany funs (arities e) }

-- | Add functions arities and name. This also works for constructors
addFuns :: [(Name,Int)] -> Env -> Env
addFuns funs = bindFunVars (map fst funs) FunVar
             . addArities funs

-- | Add a datatype's constructor given the arities
--   Projections are also generated
addCons :: [(Name,Int)] -> Env -> Env
addCons cs e = bindFunVars (map fst cs) ConVar $ addArities cs
             $ e { conFam  = insertMany [(c,cs') | c <- cs'] (conFam e)
                 , conProj = insertMany (map projName cs) (conProj e) }
  where
    cs' = map fst cs
    projName :: (Name,Int) -> (Name,[Name])
    projName (c,n) = (c,["proj" ++ show x ++ c | x <- [0..n-1]])

-- | Mark a pointer as used
useFunPtr :: Name -> ToTPTP ()
useFunPtr fn = TM $ modify $ \s -> s { usedFunPtrs = S.insert fn (usedFunPtrs s) }

-- | Make a number of new variable names
makeVarNames :: Int -> [T.VarName]
makeVarNames n = [ T.VarName ('X' : show x) | x <- [0..n-1] ]

-- | Fold the function app over the arguments
--
-- > appFold f [x,y,z] = app(app(app(f,x),y),z)
-- > appFold f []      = f
appFold :: T.Term -> [T.Term] -> T.Term
appFold = foldl (\f x -> T.Fun (T.FunName "app") [f,x])

-- | All FOL declarations from an environment and state
envStDecls :: Env -> St -> [T.Decl]
envStDecls e s = projDecls (conProj e) ++ ptrDecls (arities e) (usedFunPtrs s)

-- | Make projection declarations
projDecls :: Map Name [Name] -> [T.Decl]
projDecls = concatMap (uncurry mkDecl) . M.toList
  where
    mkDecl :: Name -> [Name] -> [T.Decl]
    mkDecl c ps = zipWith (\x p -> T.Axiom ("axiom" ++ p)
                                 $ T.Forall xs $ T.EqOp
                                      (T.Fun (T.FunName p)
                                         [T.Fun (T.FunName c) (map T.Var xs)])
                                      (T.:==)
                                      (T.Var x))
                          xs ps
      where arity = length ps
            xs    = makeVarNames arity

-- | Make pointer declarations
ptrDecls :: Map Name Int -> Set Name -> [T.Decl]
ptrDecls arities = map mkDecl . S.toList
  where
    mkDecl fn = T.Axiom ("ptr" ++ fn)
              $ T.Forall xs
                $ T.EqOp (appFold (T.Var (T.VarName (makePtrName fn)))
                                   (map T.Var xs))
                         (T.:==)
                         (T.Fun (T.FunName fn) (map T.Var xs))
      where arity = arities M.! fn
            xs    = makeVarNames arity
