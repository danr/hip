{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleContexts,TemplateHaskell #-}
module Language.HFOL.FromHaskell.Monad where

import Language.HFOL.Core

import Control.Applicative
import Control.Monad.Error
import Control.Monad.RWS hiding (gets,modify,local)
import Data.Label.PureM

import Data.Label (mkLabels)

import Data.Either (partitionEithers)

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

data St = St { _namesupply :: [Int] }
$(mkLabels [''St])

data Env = Env { _scope :: [String] }
$(mkLabels [''Env])

initSt :: St
initSt = St { _namesupply = [0..] }

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

localScope :: Name -> FH a -> FH a
localScope n m = do
  local scope (n:) m

write :: String -> FH ()
write = tell . return . Left

warn :: String -> FH ()
warn = write . ("Warning: " ++)

fatal :: String -> FH a
fatal = throwError

decl :: Decl -> FH ()
decl = tell . return . Right
