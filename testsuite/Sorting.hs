
module Sorting where

import AutoPrelude

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

len :: [a] -> Nat
len [] = Z
len (_:xs) = S (len xs)


count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    False -> count x ys

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

insort :: Nat -> [Nat] -> [Nat]
insort n [] = [n]
insort n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insort n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

prop_20 :: [Nat] -> Prop Nat
prop_20 xs
  = len (sort xs) =:= len xs

prop_78 :: [Nat] -> Prop Bool
prop_78 xs
  = proveBool (sorted (sort xs))

prop_53 :: Nat -> [Nat] -> Prop Nat
prop_53 n xs
  = count n xs =:= count n (sort xs)

