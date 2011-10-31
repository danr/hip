{-# LANGUAGE DeriveDataTypeable, TypeFamilies #-}
module Main where

import Data.Typeable

import Test.QuickCheck
import Test.QuickSpec

data Nat = Z | S Nat 
  deriving (Show,Eq,Ord,Typeable)
           
instance Enum Nat where
  toEnum 0 = Z
  toEnum n | n < 0 = error "No negative Nats"
  toEnum n = S (toEnum (pred n))
  fromEnum Z = 0
  fromEnum (S n) = succ (fromEnum n)

zero  = Z
one   = S zero
two   = S one
three = S two

-- Do we need to manually eta-expand all definitions?
inc :: Nat -> Nat
inc x = S x

plus :: Nat -> Nat -> Nat
plus Z     m = m
plus (S n) m = S (plus n m)

mult :: Nat -> Nat -> Nat
mult Z     m = Z
mult (S n) m = plus m (mult n m)

instance Arbitrary Nat where
  arbitrary = sized $ \s -> do
    x <- choose (0,round (sqrt (toEnum s)))
    return (toEnum x)
    
instance Classify Nat where
  type Value Nat = Nat
  evaluate = return
  
    
spec_module = describe "Nats"
              [ var "x" natType
              , var "y" natType
              , var "z" natType
              , con "zero" Z  
              , con "suc" S
              , con "+" plus
              , con "*" mult
              ]                
  where natType = (undefined :: Nat)
        
run_spec = quickSpec spec_module True

main = run_spec

prop_plus :: Nat -> Nat -> Bool
prop_plus n m = fromEnum (plus n m) == fromEnum n + fromEnum m

prop_mult :: Nat -> Nat -> Bool
prop_mult n m = fromEnum (mult n m) == fromEnum n * fromEnum m



