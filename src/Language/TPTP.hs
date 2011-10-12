{-# LANGUAGE FlexibleInstances #-}
module Language.TPTP where

import Data.Map (Map)
import qualified Data.Map as M

type Arity = Int

newtype FunName = FunName { funName :: String } deriving (Eq,Ord)
newtype RelName = RelName { relName :: String } deriving (Eq,Ord)
newtype VarName = VarName { varName :: String } deriving (Eq,Ord)

instance Show FunName where show = funName
instance Show RelName where show = relName
instance Show VarName where show = varName

data Language = Language 
              { functions :: Map FunName Arity
              , relations :: Map RelName Arity
              }
  deriving (Show)

data Term = Fun FunName [Term]
          | Var VarName
  deriving (Eq,Ord,Show)

data BinOp = (:&) | (:|) | (:=>) | (:<=>)
  deriving (Eq,Ord,Show)

data Formula = Term :== Term       -- atomic
             | Rel RelName [Term] -- atomic
             | Neg Formula
             | BinOp Formula BinOp Formula
             | Forall [VarName] Formula
             | Exists [VarName] Formula
  deriving (Eq,Ord,Show)

mkBinOp op phi psi = BinOp phi op psi

infix 4 ===
infixr 3 &
infixr 3 :&
infixr 3 /\
infixr 2 \/
infixr 2 :|
infixl 1 ==>
infixl 1 :=>
infix  1 <=>

(==>) = mkBinOp (:=>)
(&) = mkBinOp (:&)
(/\) = mkBinOp (:&)
(\/) = mkBinOp (:|)
(<=>) = mkBinOp (:<=>)

(===) = (:==)

data Decl = Axiom      Formula
          | Conjecture Formula
  deriving (Eq,Ord,Show)

class Quantifier t where
    quantifier 
        :: ([VarName] -> Formula -> Formula) -- ^ quantifier, Forall or Exists
        -> [VarName]                         -- ^ accumulated used variables
        -> [VarName]                         -- ^ variable pool
        -> t                                 -- ^ Formula or (Term -> t)
        -> Formula                           -- ^ resulting formula
 
instance Quantifier Formula where
    quantifier q _ acc f = q (reverse acc) f
 
instance Quantifier r => Quantifier (Term -> r) where
    quantifier q (v:vs) acc f = quantifier q vs (v:acc) (f (Var v))
 
forall :: (Quantifier t) => t -> Formula
forall = quantifier Forall [VarName ("X" ++ show x) | x <- [0..]] []

exists :: (Quantifier t) => t -> Formula
exists = quantifier Exists [VarName ("X" ++ show x) | x <- [0..]] []

example :: Formula
example = forall $ \x y z -> x === y & y === z ==> x === z