{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleContexts,TemplateHaskell #-}
module Language.HFOL.FromHaskell.Monad where

import Language.HFOL.Core

import Control.Applicative
import Control.Monad.Error
import Control.Monad.RWS hiding (gets,modify,local,asks)
import Data.Label.PureM

import qualified Data.Map as M
import Data.Map (Map)

import Data.Label (mkLabels)
import Data.Either (partitionEithers)
import Data.List (intercalate)

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

data St = St { _namesupply :: [Int]
             , _binds      :: Map Name Expr
             }
$(mkLabels [''St])

data Env = Env { _scope :: [String] }
$(mkLabels [''Env])

initSt :: St
initSt = St { _namesupply = [0..]
            , _binds      = M.empty
            }

initEnv :: Env
initEnv = Env { _scope = [] }

newtype FH a = FH (ErrorT String (RWS Env [Either String Decl] St) a)
  deriving(Functor,Applicative,Monad
          ,MonadWriter [Either String Decl]
          ,MonadReader Env
          ,MonadState St
          ,MonadError String)

runFH :: FH () -> (Either String [Decl],[String])
runFH (FH m) = case evalRWS (runErrorT m) initEnv initSt of
  (Left err,w) -> (Left err,fst (partitionEithers w))
  (Right (),w) -> let (msgs,decls) = partitionEithers w
                  in  (Right decls,msgs)

localScopeName :: Name -> FH a -> FH a
localScopeName n = local scope (n:)

localBindScope :: FH a -> FH a
localBindScope m = do
  bs <- gets binds
  r <- m
  puts binds bs
  return r

namesInScope :: FH [Name]
namesInScope = M.keys <$> gets binds

addBind :: Name -> Name -> [Name] -> FH ()
addBind fname scopedfname args = modify binds (M.insert fname e)
  where e | null args = Var scopedfname
          | otherwise = App scopedfname (map Var args)

lookupBind :: Name -> FH (Maybe Expr)
lookupBind n = M.lookup n <$> gets binds

scopePrefix :: Name -> FH Name
scopePrefix n = do
  s <- asks scope
  if null s then return n
            else do u <- newUnique
                    let delim = "_"
                    return (intercalate delim (reverse s) ++ delim ++ n )
                           {- ++ delim ++  show u) -}

newUnique :: FH Int
newUnique = do
  x:xs <- gets namesupply
  puts namesupply xs
  return x

write :: String -> FH ()
write = tell . return . Left

warn :: String -> FH ()
warn = write . ("Warning: " ++)

fatal :: String -> FH a
fatal = throwError

decl :: Decl -> FH ()
decl = tell . return . Right

debug :: String -> FH ()
debug = write . ("Debug: " ++)