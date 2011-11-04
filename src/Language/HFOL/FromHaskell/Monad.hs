{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleContexts,TemplateHaskell #-}
module Language.HFOL.FromHaskell.Monad where

import Language.HFOL.Core as C
import Language.Haskell.Exts as H hiding (Name,Decl)

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
             , _binds      :: Map Name Exp
             , _scope      :: [Name]
             }
$(mkLabels [''St])

data Env = Env { _scopeName :: [String] }
$(mkLabels [''Env])

initSt :: St
initSt = St { _namesupply = [0..]
            , _binds      = M.empty
            , _scope      = []
            }

initEnv :: Env
initEnv = Env { _scopeName = [] }

newtype FH a = FH (ErrorT String (RWS Env [Either String Decl] St) a)
  deriving(Functor,Applicative,Monad
          ,MonadWriter [Either String Decl]
          ,MonadReader Env
          ,MonadState St
          ,MonadError String)

runFH :: FH () -> (Either String [Decl],[String])
runFH (FH m) = case evalRWS (runErrorT m) initEnv initSt of
  (r,w) -> let (msgs,decls) = partitionEithers w
           in  (case r of
                   Right () -> Right decls
                   Left err -> Left err
               ,msgs)

localScopeName :: Name -> FH a -> FH a
localScopeName n = local scopeName (n:)

localBindScope :: FH a -> FH a
localBindScope m = do
  bs <- gets binds
  r <- m
  puts binds bs
  return r

addToScope :: Name -> FH ()
addToScope = modify scope . (:)

namesInScope :: FH [Name]
namesInScope = liftM2 (++) (M.keys <$> gets binds) (gets scope)

addBind :: Name -> Name -> [Name] -> FH Exp
addBind fname scopedfname args
    | fname == scopedfname = if null args
                                 then do warn $ "occurs check: " ++ fname
                                         return (var fname)
                                 else fatal $ "occurs check: " ++ fname
    | otherwise = do modify binds (M.insert fname e)
                     debug $ "addBind: " ++ fname ++ " to " ++ show e
                     return e
  where e = foldl H.App (var scopedfname) (map var args)
        var = H.Var . H.UnQual . H.Ident

lookupBind :: Name -> FH (Maybe Exp)
lookupBind n = M.lookup n <$> gets binds

scopePrefix :: Name -> FH Name
scopePrefix n = do
  s <- asks scopeName
  if null s then return n
            else do _u <- newUnique
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
fatal = throwError . ("Fatal: " ++)

decl :: Decl -> FH ()
decl = tell . return . Right

debug :: String -> FH ()
debug = write . ("Debug: " ++)