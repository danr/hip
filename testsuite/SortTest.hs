module SortTest where

import AutoPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),Int,return)

otherwise = True

(<.) :: Bool -> Bool -> Bool
False <. True = True
_     <. _    = False

(=.) :: Bool -> Bool -> Bool
True  =. True  = True
False =. False = True
_     =. _     = False

data Nat = Z | S Nat deriving (Eq,Show)

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

True  && a = a
False && _ = False

False || a = a
True  || _ = True

length :: [a] -> Nat
length [] = Z
length (_:xs) = S (length xs)

count :: Bool -> [Bool] -> Nat
count x [] = Z
count x (y:ys) =
  case x =. y of
    True  -> S (count x ys)
    False -> count x ys

sorted :: [Bool] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = ((x =. y) || (x <. y)) && sorted (y:ys)

insert :: Bool -> [Bool] -> [Bool]
insert n [] = [n]
insert n (x:xs) | n <. x    = n : x : xs
                | otherwise = x : insert n xs

sort :: [Bool] -> [Bool]
sort [] = []
sort (x:xs) = insert x (sort xs)

prop_20 :: [Bool] -> Prop Nat
prop_20 xs
  = length (sort xs) =:= length xs

prop_78 :: [Bool] -> Prop Bool
prop_78 xs
  = sorted (sort xs) =:= True

prop_53 :: Bool -> [Bool] -> Prop Nat
prop_53 x xs
  = count x xs =:= count x (sort xs)

main = do
  quickCheck (printTestCase "prop_20" (prop_20 :: [Bool] -> Prop Nat))
  quickCheck (printTestCase "prop_78" (prop_78 :: [Bool] -> Prop Bool))
  quickCheck (printTestCase "prop_53" (prop_53 :: Bool -> [Bool] -> Prop Nat))
