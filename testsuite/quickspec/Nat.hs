{-# LANGUAGE DeriveDataTypeable, TypeFamilies, CPP #-}
module Main where

import Data.Typeable

import Hip.HipSpec

import Test.QuickCheck

import Prelude hiding ((+),(*))

data Nat = Z | S Nat deriving (Show,Eq,Ord,Typeable)

zero  = Z
one   = S zero
two   = S one
three = S two

inc :: Nat -> Nat
inc x = S x

(+) :: Nat -> Nat -> Nat
Z   + m = m
S n + m = S (n + m)

(*) :: Nat -> Nat -> Nat
Z   * m = Z
S n * m = m + (n * m)

main = hipSpec "Nat.hs" conf 3
  where conf = describe "Nats"
               [ var "x" natType
               , var "y" natType
               , var "z" natType
               , con "Z" Z
               , con "S" S
               , con "+" (+)
               , con "*" (*)
               ]
           where natType = (undefined :: Nat)

instance Enum Nat where
  toEnum 0 = Z
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

instance Arbitrary Nat where
  arbitrary = sized $ \s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x)

instance Classify Nat where
  type Value Nat = Nat
  evaluate = return


