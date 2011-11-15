module Language.HFOL.ToFOL.InductionPrinciples where

import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.ParserInternals
import Language.HFOL.ToFOL.Pretty

import Data.List
import Data.Maybe (fromMaybe)
import Control.Arrow

type ConName = Name
type VarName = Name
type TypeName = Name

type Env = [(TypeName,[(Name,Type)])]

testEnv :: Env
testEnv = map (declName &&& conTypes) $ parseDecls $ concatMap (++ ";")
  [ "data Tree a = Branch (Tree a) a (Tree a) | Empty"
  , "data Nat = Suc Nat | Zero"
  , "data List a = Cons a (List a) | Nil"
  , "data Expr = Add Expr Expr | Mul Expr Expr | Value Nat | X | Neg Expr"
  , "data Integ = PS Nat | NS Nat | Z"
  ]

data Part = Part { hypotheses :: [Expr] , conjecture :: Expr }
  deriving (Eq,Ord)

instance Show Part where
  show (Part hyps conj) = case hyps of
     []   -> p conj
     hyps -> foldr1 (\xs ys -> xs ++ " & " ++ ys) (map p hyps)
             ++ " => " ++ p conj
    where p e = "P(" ++ prettyCore e ++ ")"

-- | Conrete types are types like Nat, Tree a, but not a or Nat -> Nat
concreteType :: Type -> Bool
concreteType TyCon{} = True
concreteType _       = False

-- | Which arguments to this constructor are recursive?
--
--   For example, Branch :: Tree a -> a -> Tree a -> Tree a is
--   recursive in its first and third argument, as it is the same as
--   the resulting type, so the result of this function will be
--   [True,False,True]
recursiveArgs :: Type -> [Bool]
recursiveArgs (TyApp ts) = let resType = last ts
                           in  map (== resType) (init ts)
recursiveArgs _          = []

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

{- multi-variable
induction :: [(VarName,TypeName)]
          -> [(TypeName,[(Name,Type)])]
          -> [[Expr]]
-}