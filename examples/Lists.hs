-- Properties come from QuickSpec
module Lists where

import Prelude ()

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

point :: a -> [a]
point x = [x]

reverse :: [a] -> [a]
reverse (x:xs) = reverse xs ++ point x
reverse []     = []

reverse2 :: [a] -> [a]
reverse2 = revAcc []

revAcc :: [a] -> [a] -> [a]
revAcc acc []     = acc
revAcc acc (x:xs) = revAcc (x:acc) xs

prop_00 :: a -> [a] -> Prop [a]
prop_00 x xs = x:xs =:= revAcc xs (point x)

prop_01 :: [a] -> [a] -> Prop [a]
prop_01 xs ys = ys ++ xs =:= revAcc xs (reverse ys)

prop_02 :: [a] -> [a] -> Prop [a]
prop_02 xs ys = revAcc ys xs =:= reverse xs ++ ys

prop_03 :: [a] -> [a] -> Prop [a]
prop_03 xs ys = ys ++ xs =:= revAcc xs (reverse2 ys)

prop_04 :: [a] -> [a] -> Prop [a]
prop_04 xs ys = revAcc ys xs =:= reverse2 xs ++ ys

prop_05 :: [a] -> Prop [a]
prop_05 xs = reverse2 xs =:= reverse xs

prop_06 :: a -> Prop [a]
prop_06 x = x:[] =:= point x

prop_07 :: [a] -> Prop [a]
prop_07 xs = xs ++ [] =:= xs

prop_08 :: [a] -> Prop [a]
prop_08 xs = revAcc xs [] =:= xs

prop_09 :: [a] -> Prop [a]
prop_09 xs = [] ++ xs =:= xs

prop_10 :: [a] -> Prop [a]
prop_10 xs = revAcc [] xs =:= reverse xs

prop_11 :: [a] -> Prop [a]
prop_11 xs = revAcc [] xs =:= reverse2 xs

prop_12 :: a -> [a] -> [a] -> Prop [a]
prop_12 x xs ys = (x:xs) ++ ys =:= x:(xs ++ ys)

prop_13 :: [a] -> [a] -> [a] -> Prop [a]
prop_13 xs ys zs = (xs ++ ys) ++ zs =:= xs ++ (ys ++ zs)

prop_14 :: [a] -> [a] -> [a] -> Prop [a]
prop_14 xs ys zs = revAcc xs ys ++ zs =:= revAcc zs (revAcc ys xs)

prop_15 :: a -> [a] -> [a] -> Prop [a]
prop_15 x xs ys = revAcc (x:xs) ys =:= revAcc xs (x:ys)

prop_16 :: [a] -> [a] -> [a] -> Prop [a]
prop_16 xs ys zs = revAcc (revAcc xs ys) zs =:= revAcc xs (ys ++ zs)