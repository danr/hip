{-# LANGUAGE FlexibleContexts, PatternGuards, ViewPatterns #-}
module Autospec.ToFOL.InductionPrinciples where

import Autospec.ToFOL.Core
import Autospec.ToFOL.ParserInternals
import Autospec.ToFOL.Pretty

import Data.List
import Data.Maybe (fromMaybe)
import Data.Generics.Uniplate.Data

import Control.Arrow
import Control.Monad
import Control.Monad.State

type ConName = Name
type VarName = Name
type TypeName = Name

type Env = [(TypeName,[(Name,Type)])]

testEnv :: Env
testEnv = map (declName &&& conTypes) $ parseDecls $ concatMap (++ ";")
  [ "data Tree a = Branch (Tree a) a (Tree a) | Empty"
  , "data T = B T T | E"
  , "data Nat = Suc Nat | Zero"
  , "data List a = Cons a (List a) | Nil"
  , "data Expr = Add Expr Expr | Mul Expr Expr | Value Nat | X | Neg Expr"
  , "data Integ = PS Nat | NS Nat | Z"
  , "data Tup a b = Tup a b"
  , "data Either a b = Left a | Right b"
  , "data Bool = True | False"
  , "data Maybe a = Just a | Nothing"
  , "data Unit = Unit"
  , "data Ord = Zero | Suc Ord | Lim (Nat -> Ord)"
  , "data WrapList a = Wrap (List a)"
  ]

data Part = Part { hypotheses :: [Expr] , conjecture :: Expr }
  deriving (Eq,Ord)

instance Show Part where
  show (Part hyps conj) = case hyps of
     []   -> p conj
     hyps -> foldr1 (\xs ys -> xs ++ " & " ++ ys) (map p hyps)
             ++ " => " ++ p conj
    where p e = "P(" ++ prettyCore e ++ ")"

prints :: Show a => [a] -> IO ()
prints = mapM_ print

simpleInduction :: VarName -> TypeName -> Env -> [Part]
simpleInduction var ty env = do
    let cons = fromMaybe (error $ "unknown datatype " ++ show ty)
                         (lookup ty env)
    (con,conTy) <- cons
    let recs = recursiveArgs conTy
        vars = map (Var . (var ++) . show) [0..length recs-1]
        hyps = [ v | (v,r) <- zip vars recs, r ]
        step = Con con vars
    return (Part hyps step)

-- For each constructor, unroll each typed variable to all its
-- constructors.

newVar :: (MonadState Int m,Monad m) => m Int
newVar = do
    x <- get
    modify succ
    return x

iterateM :: Monad m => Int -> (a -> m a) -> a -> m a
iterateM 0 f x = return x
iterateM n f x = do y <- f x
                    iterateM (n - 1) f y

substType :: [(Name,Type)] -> Type -> Type
substType s = transform f
  where
    f (TyVar x) | Just t <- lookup x s = t
    f t                                = t

unTyVar :: Type -> Name
unTyVar (TyVar x) = x
unTyVar t         = error $ "unTyVar: " ++ show t

instantiate :: Type -> Env -> Maybe [(Name,Type)]
instantiate (TyCon n ts) env | Just cons <- lookup n env = Just (map (uncurry inst) cons)
  where
    inst :: Name -> Type -> (Name,Type)
    inst n t = case resTy of
                   TyCon _ (map unTyVar -> as) ->
                       -- as is for instance ["a","b","c"]
                       -- ts could be [Nat,List a,b -> c]
                       let instMap = zip as ts
                       in  (n,TyApp [ substType instMap c | c <- conList ++ [resTy] ])
                   _  -> (n,t)
      where
        resTy   :: Type
        conList :: [Type]
        (conList,resTy) = case t of
                       TyApp xs -> (init xs,last xs)
                       _        -> ([],t)
instantiate _ _ = Nothing

unroll :: Int -> [Expr] -> Env -> [[Expr]]
unroll i es env = evalStateT (iterateM i (mapM (transformM go)) es) 0
  where
    go :: Expr -> StateT Int [] Expr
    go (Var v ::: t) =
       case instantiate t env of
          Nothing   -> return (Var v ::: t)
          Just cons -> do
              (con,conTy) <- lift cons
              let conList = case conTy of
                                TyApp xs -> init xs
                                _        -> []
              args <- forM conList $ \t' -> do
                          n <- newVar
                          return (Var (v ++ '.':show n) ::: t')
              return (Con con args)
    go e = return e
