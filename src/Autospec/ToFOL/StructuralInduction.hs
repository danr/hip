{-# LANGUAGE FlexibleContexts, PatternGuards, ViewPatterns #-}
module Autospec.ToFOL.StructuralInduction where

import Autospec.ToFOL.Core
import Autospec.ToFOL.ParserInternals
import Autospec.ToFOL.Pretty
import Autospec.ToFOL.Constructors
import Autospec.Util

import Data.List hiding (partition)
import Data.Maybe (fromMaybe)
import Data.Generics.Uniplate.Data

import Control.Arrow
import Control.Monad
import Control.Monad.State

import Test.QuickCheck

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
  , "data Z = P Nat | N Nat"
  ]

data IndPart = IndPart { hypotheses :: [[Expr]]
                       , conjecture :: [Expr]
                       , vars       :: [Name]
                       }
  deriving (Eq,Ord)

instance Show IndPart where
  show (IndPart hyps conj _) = case hyps of
     []   -> p conj
     hyps -> foldr1 (\xs ys -> xs ++ " & " ++ ys) (map p hyps)
             ++ " => " ++ p conj
    where p es = "P(" ++ intercalate "," (map prettyCore es) ++ ")"

prints :: Show a => [a] -> IO ()
prints = mapM_ print

simpleInduction :: VarName -> TypeName -> Env -> [IndPart]
simpleInduction var ty env = do
    let cons = fromMaybe (error $ "unknown datatype " ++ show ty)
                         (lookup ty env)
    (con,conTy) <- cons
    let recs = recursiveArgs conTy
        vars = map (Var . (var ++) . show) [0..length recs-1]
        hyps = [ [v] | (v,r) <- zip vars recs, r ]
        step = [Con con vars]
    return (IndPart hyps step [var])

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

bottomless :: Expr -> Bool
bottomless e = and [ False | Var x <- universe e, x == bottomName ]

instantiate :: Type -> Env -> Maybe [(Name,Type)]
instantiate (TyCon n ts) env
    | Just cons <- lookup n env = Just (map (uncurry inst) cons)
  where
    inst :: Name -> Type -> (Name,Type)
    inst n t = case resTy of
                   TyCon _ (map unTyVar -> as) ->
                       -- as is for instance ["a","b","c"]
                       -- ts could be [Nat,List a,b -> c]
                       let instMap = zip as ts
                       in  (n,foldr1 tapp [ substType instMap c | c <- argsTy ++ [resTy] ])
                   _  -> (n,t)
      where
        resTy   :: Type
        argsTy :: [Type]
        (argsTy,resTy) = case t of
                       TyApp xs -> (init xs,last xs)
                       _        -> ([],t)
instantiate _ _ = Nothing

-- | For each constructor, unroll each typed variable to all its
--   constructors.
unroll :: [Expr] -> Env -> Int -> [[Expr]]
unroll es env i = evalStateT (iterateM i (mapM (transformM go)) es) 0
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

-- partInts n k parts n into k elements
partInts :: Int -> Int -> [[Int]]
partInts 0 0 = [[]]
partInts n k | k < 0 = []
partInts n k = [ m : k | m <- [1..n], k <- partInts (n - m) (k - 1) ]

prop_partInts_sum :: Int -> Int -> Bool
prop_partInts_sum n k = all ((n ==) . sum) (partInts n k)

prop_partInts_length :: Int -> Int -> Bool
prop_partInts_length n k = all ((k ==) . length) (partInts n k)

partitionTo :: Env -> [(Name,Type)] -> Type -> Int -> [Expr]
partitionTo env vs t = concatMap (partition env vs t) . enumFromTo 1

partition :: Env -> [(Name,Type)] -> Type -> Int -> [Expr]
partition env vs t n
  | n <= 0 = []
  | n == 1 = [ Var n | (n,t') <- vs, t' == t {- warning: List a /= List Nat -}]
          ++ [ Con con [] | Just cons <- [instantiate t env]
                          , (con,conTy) <- cons
                          , conTy == t
                          ]
  | Just cons <- instantiate t env = do
      (con,conTy) <- cons
      case conTy of
         TyApp xs -> do
           part <- partInts (n - 1) (length xs - 1)
           args <- zipWithM (partition env vs) (init xs) part
           return (Con con args)
         _  -> []
  | otherwise = []

subdiag :: [Int] -> [[Int]]
subdiag [] = []
subdiag (x:xs) = (if x > 1 then ((x-1:xs) :) else id)
                 [ x : ys | ys <- subdiag xs ]

partitionListTo :: Env -> [[(Name,Type)]] -> [Type] -> [Int] -> [[Expr]]
partitionListTo env vs ts ps = do
    part <- subdiag ps
    sequence (zipWith3 (partitionTo env) vs ts part)

testVars = [("x",parseType "Nat"),("y",parseType "Nat"),("xs",parseType "List Nat")]

testVars' = [("x",parseType "Nat"),("y",parseType "Nat")]

natType = parseType "Nat"

testType = parseType "List Nat"

testType' = parseType "Z"

testPartition = partition testEnv testVars testType

constructors :: Expr -> Int
constructors e = sum $ [ 1 | Con{}  <- universe e ]
                    ++ [ 1 | Var{} <- universe e ]


typedVars :: Expr -> [(Name,Type)]
typedVars e = [ (v,t) | Var v ::: t <- universe e ]

-- | Leads to combinatorial explosion (Tree a with depth 2)
structuralInduction :: [(VarName,Type)] -> Env -> Int -> [IndPart]
structuralInduction vts env depth = map mkPart ess
   where
     ess :: [[Expr]]
     ess = unroll (map (uncurry ((:::) . Var)) vts) env depth

     mkPart :: [Expr] -> IndPart
     mkPart es = IndPart (nubSorted (partitionListTo env vs ts ps))
                         (map stripTypes es)
                         (map (concat . map fst) vs)
       where
          vs :: [[(Name,Type)]]
          vs = map typedVars es
          ts = map snd vts
          ps = map (constructors) es

