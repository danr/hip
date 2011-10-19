{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.HFOL.ToTPTPMonad where

import Language.HFOL.Core
import Language.HFOL.RemoveOverlap
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

newtype ToTPTP a = MkToTPTP { unToTPTP :: ReaderT Env (State St) a }
  deriving (Functor,Applicative,Monad,MonadState St,MonadReader Env)

runTPTP :: Env -> ToTPTP a -> (a,St)
runTPTP env m = runState (runReaderT (unToTPTP m) env) emptySt

data Env = Env { arities   :: Map Name Int
                 -- ^ Arity of functions and constructors
               , boundVars :: Map Name (Either FunName VarName)
                 -- ^ TPTP name of functions and constructors and quantified variables)
               , conProj   :: Map Name [Name]
                 -- ^ Projection functions for constructors
               , conFam    :: Map Name [Name]
                 -- ^ The other constructors for a given constructor
               }

data St = St { usedFnPtrs :: Set Name
               -- ^ Which functions we need to produce ptr conversions for
             }

-- | The empty environment
emptyEnv = Env M.empty M.empty M.empty M.empty

-- | The empty state
emptySt = St S.empty

-- | Insert /n/ elements to a map
--   /O(n * log(n))/
insertMany :: Ord k => [(k,v)] -> Map k v -> Map k v
insertMany kvs m = foldr (uncurry M.insert) m kvs

-- | Looks up if a name is a variable or a function/constructor
lookupVar :: Name -> ToTPTP (Either FunName VarName)
lookupVar n = asks (fromMaybe (error $ "lookupVar, unbound: " ++ n)
                   . M.lookup n . boundVars)

-- | Looks up an arity of a function or constructor
lookupArity :: Name -> ToTPTP Int
lookupArity n = asks (fromMaybe (error $ "lookupArity, unbound: " ++ n)
                     . M.lookup n . arities)

-- | Bind names to variables and perform an action
bindVars :: [Name] -> [VarName] -> ToTPTP a -> ToTPTP a
bindVars ns vs = local $ \e -> e
  { boundVars = insertMany (zipWith (\n v -> (n,Right v)) ns vs) (boundVars e) }

-- | Make a pointer name of a name
makePtrName :: Name -> Name
makePtrName n = n ++ "_ptr"

-- | Make a pointer of a function name
makeFunPtrName :: FunName -> FunName
makeFunPtrName = FunName . makePtrName . funName

-- | Add a functions arities and name
addFuns :: [(Name,Int)] -> Env -> Env
addFuns funs e = e
    { arities   = insertMany funs (arities e)
    , boundVars = insertMany [(n,Left (FunName n))| (n,_) <- funs] (boundVars e)
    }

-- | Add a datatype's constructor given the arities
--   Projections  are also generated
addCons :: [(Name,Int)] -> Env -> Env
addCons cs e = addFuns cs
             $ e { conFam  = insertMany [(c,cs') | c <- cs'] (conFam e)
                 , conProj = insertMany (map projName cs) (conProj e) }
  where
    cs' = map fst cs
    projName :: (Name,Int) -> (Name,[Name])
    projName (c,n) = (c,["proj" ++ show x ++ c | x <- [0..n-1]])

-- | Mark a pointer as used
useFnPtr :: Name -> ToTPTP ()
useFnPtr fn = modify $ \s -> s { usedFnPtrs = S.insert fn (usedFnPtrs s) }

-- | Make new variable names
makeVarNames n = [ T.VarName ('X' : show x) | x <- [0..n-1] ]

-- | All FOL declarations from an environment and state
envStDecls :: Env -> St -> [T.Decl]
envStDecls e s = projDecls (conProj e) ++ ptrDecls (arities e) (usedFnPtrs s)

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

-- | Fold the function app over the arguments
-- > appFold f [x,y,z] = app(app(app(f,x),y),z)
-- > appFold f []      = f
appFold :: T.Term -> [T.Term] -> T.Term
appFold = foldl (\f x -> T.Fun (T.FunName "app") [f,x])

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
