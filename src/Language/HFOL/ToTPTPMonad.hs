{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.HFOL.ToTPTPMonad where

import Language.HFOL.Core
import Language.HFOL.RemoveOverlap
import qualified Language.TPTP as T
import Language.TPTP.Pretty

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

data Env = Env { fnArity :: Map Name Int
                 -- ^ Arity of functions
               , conProj :: Map Name [Name]
                 -- ^ Projection functions for constructors
               , conFam :: Map Name [Name]
                 -- ^ The other constructors for a given constructor
               }

data St = St { usedFnPtrs :: Set Name }

-- | Make a pointer name of a function name
makeFunPtrName :: Name -> Name
makeFunPtrName n = n ++ "_ptr"

-- | Add all the constructors for a type
addCons :: [Name] -> Env -> Env
addCons cs e = e { conFam = foldr (\c -> M.insert c cs) (conFam e) cs }

-- | Add all projections for a constructor
addProj :: Name -> [Name] -> Env -> Env
addProj c ps e = e { conProj = M.insert c ps (conProj e) }

-- | Automatically make projections for a constructor of a given arity
addProj' :: Name -> Int -> Env -> Env
addProj' c n = addProj c [ "proj" ++ c ++ show x | x <- [0..n-1] ]

-- | Add a function's arity
addFnArity :: Name -> Int -> Env -> Env
addFnArity n args e = e { fnArity = M.insert n args (fnArity e) }

-- | All FOL declarations from an environment and state
envStDecls :: Env -> St -> [T.Decl]
envStDecls e s = projDecls (conProj e) ++ ptrDecls (fnArity e) (usedFnPtrs s)

useFnPtr :: Name -> St -> St
useFnPtr fn s = s { usedFnPtrs = S.insert fn (usedFnPtrs s) }

makeVarNames n = [ T.VarName ("X" ++ show x) | x <- [0..n-1] ]

-- | Make projection declarations
projDecls :: Map Name [Name] -> [T.Decl]
projDecls = concatMap (uncurry mkDecl) . M.toList
  where
    mkDecl :: Name -> [Name] -> [T.Decl]
    mkDecl c ps = zipWith (\x p -> T.Axiom ("proj" ++ c ++ "_" ++ p)
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
                $ T.EqOp (foldl (\f x -> T.Fun (T.FunName "app") [f,x])
                                           (T.Var (T.VarName (makeFunPtrName fn)))
                                           (map T.Var xs))
                         (T.:==)
                         (T.Fun (T.FunName fn) (map T.Var xs))
      where arity = arities M.! fn
            xs    = makeVarNames arity

emptyEnv = Env M.empty M.empty M.empty

emptySt = St S.empty

testEnvSt :: (Env,St)
testEnvSt = ( addFnArity "map" 2
            $ addFnArity "flip" 3
            $ addProj "Cons" ["head","tail"]
            $ addProj' "T4" 4
            $ addProj "Just" ["fromJust"] emptyEnv
            , useFnPtr "flip"
            $ useFnPtr "map" emptySt
            )

testDecls :: [T.Decl]
testDecls = uncurry envStDecls testEnvSt

testIO :: IO ()
testIO = putStrLn (pretty testDecls)

newtype ToTPTP a = MkToTPTP { runToTPTP :: ReaderT Env (State St) a }
  deriving (Functor,Applicative,Monad,MonadState St,MonadReader Env)
