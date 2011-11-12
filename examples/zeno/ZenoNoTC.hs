-- Taken from http://www.doc.ic.ac.uk/~ws506/tryzeno/comparison/Comparison.hs

{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, ExistentialQuantification #-}

module ZenoNoTC where

import Prelude ()
-- import Zeno

data Bool = True | False

infix 1 :=:
infixr 0 $

($) :: (a -> b) -> a -> b
f $ x = f x

otherwise :: Bool
otherwise = True

data Equals
  = forall a . (:=:) a a

data Prop
  = Given Equals Prop
  | Prove Equals

prove :: Equals -> Prop
prove = Prove

given :: Equals -> Prop -> Prop
given = Given

proveBool :: Bool -> Prop
proveBool p = Prove (p :=: True)

givenBool :: Bool -> Prop -> Prop
givenBool p = Given (p :=: True)

data Nat = Z | S Nat
data Tree a = Leaf | Node (Tree a) a (Tree a)

-- Boolean functions

not :: Bool -> Bool
not True = False
not False = True

(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False


{-
-- Type class for equality
class Eq a where
  (==) :: a -> a -> Bool

-- Type class for ordered
class Ord a where
  (<=), (<) :: a -> a -> Bool

-- Type class for numbers
class Num a where
  (+), (*), (-), min, max :: a -> a -> a
-}

-- Natural numbers

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

Z     * _ = Z
(S x) * y = y + (x * y)

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

max Z     y     = y
max x     Z     = x
max (S x) (S y) = S (max x y)

-- List functions

(=:=) :: [Nat] -> [Nat] -> Bool
[]     =:= []     = True
(x:xs) =:= []     = False
[]     =:= (y:ys) = False
(x:xs) =:= (y:ys) = x == y && (xs =:= ys)

null :: [a] -> Bool
null [] = True
null _  = False

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n == x of
    True -> delete n xs
    False -> x : (delete n xs)

len :: [a] -> Nat
len [] = Z
len (_:xs) = S (len xs)

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) =
  case n == x of
    True -> True
    False -> elem n xs

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take :: Nat -> [a] -> [a]
take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    False -> count x ys

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    False -> []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    False -> x:xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    False -> filter p xs

init :: [a] -> [a]
init [] = []
init [x] = []
init (x:xs) = x:(init xs)

last :: [Nat] -> Nat
last [] = Z
last [x] = x
last (x:xs) = last xs

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

ins :: Nat -> [Nat] -> [Nat]
ins n [] = [n]
ins n (x:xs) =
  case n < x of
    True -> n : x : xs
    False -> x : (ins n xs)

ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n == x of
    True -> x : xs
    False -> x : (ins1 n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

initConcat :: [a] -> [a] -> [a]
initConcat xs [] = init xs
initConcat xs ys = xs ++ init ys

lastOfTwo :: [Nat] -> [Nat] -> Nat
lastOfTwo xs [] = last xs
lastOfTwo _ ys = last ys

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

height :: Tree a -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)

prop_1_Nat_Nat_Nat x y z
  = prove (x + (y + z) :=: (x + y) + z)

prop_01 n xs
  = prove (take n xs ++ drop n xs :=: xs)

prop_02 n xs ys
  = prove (count n xs + count n ys :=: count n (xs ++ ys))

prop_03 n xs ys
  = proveBool (count n xs <= count n (xs ++ ys))

prop_04 n xs
  = prove (S (count n xs) :=: count n (n : xs))

prop_05 n x xs
  = givenBool (n == x)
  $ prove (S (count n xs) :=: count n (x : xs))

prop_06 n m
  = prove (n - (n + m) :=: Z)

prop_07 (n :: Nat) m
  = prove ((n + m) - n :=: m)

prop_08 (k :: Nat) m n
  = prove ((k + m) - (k + n) :=: m - n)

prop_09 (i :: Nat) j k
  = prove ((i - j) - k :=: i - (j + k))

prop_10 (m :: Nat)
  = prove (m - m :=: Z)

prop_11 xs
  = prove (drop Z xs :=: xs)

prop_12 n f xs
  = prove (drop n (map f xs) :=: map f (drop n xs))

prop_13 n x xs
  = prove (drop (S n) (x : xs) :=: drop n xs)

prop_14 p xs ys
  = prove (filter p (xs ++ ys) :=: (filter p xs) ++ (filter p ys))

prop_15 x xs
  = prove (len (ins x xs) :=: S (len xs))

prop_16 (x :: Nat) xs
  = givenBool (xs =:= [])
  $ prove (last (x:xs) :=: x)

prop_17 (n :: Nat)
  = prove (n <= Z :=: n == Z)

prop_18 i m
  = proveBool (i < S (i + m))

prop_19 n xs
  = prove (len (drop n xs) :=: len xs - n)

prop_20 xs
  = prove (len (sort xs) :=: len xs)

prop_21 (n :: Nat) m
  = proveBool (n <= (n + m))

prop_22 (a :: Nat) b c
  = prove (max (max a b) c :=: max a (max b c))

prop_23 (a :: Nat) b
  = prove (max a b :=: max b a)

prop_24 (a :: Nat) b
  = prove ((max a b) == a :=: b <= a)

prop_25 (a :: Nat) b
  = prove ((max a b) == b :=: a <= b)

prop_26 x xs ys
  = givenBool (x `elem` xs)
  $ proveBool (x `elem` (xs ++ ys))

prop_27 x xs ys
  = givenBool (x `elem` ys)
  $ proveBool (x `elem` (xs ++ ys))

prop_28 x xs
  = proveBool (x `elem` (xs ++ [x]))

prop_29 x xs
  = proveBool (x `elem` ins1 x xs)

prop_30 x xs
  = proveBool (x `elem` ins x xs)

prop_31 (a :: Nat) b c
  = prove (min (min a b) c :=: min a (min b c))

prop_32 (a :: Nat) b
  = prove (min a b :=: min b a)

prop_33 (a :: Nat) b
  = prove (min a b == a :=: a <= b)

prop_34 (a :: Nat) b
  = prove (min a b == b :=: b <= a)

prop_35 xs
  = prove (dropWhile (\_ -> False) xs :=: xs)

prop_36 xs
  = prove (takeWhile (\_ -> True) xs :=: xs)

prop_37 x xs
  = proveBool (not $ x `elem` delete x xs)

prop_38 n xs
  = prove (count n (xs ++ [n]) :=: S (count n xs))

prop_39 n x xs
  = prove (count n [x] + count n xs :=: count n (x:xs))

prop_40 xs
  = prove (take Z xs :=: [])

prop_41 n f xs
  = prove (take n (map f xs) :=: map f (take n xs))

prop_42 n x xs
  = prove (take (S n) (x:xs) :=: x : (take n xs))

prop_43 p xs
  = prove (takeWhile p xs ++ dropWhile p xs :=: xs)

prop_44 x xs ys
  = prove (zip (x:xs) ys :=: zipConcat x xs ys)

prop_45 x y xs ys
  = prove (zip (x:xs) (y:ys) :=: (x, y) : zip xs ys)

prop_46 xs
  = prove (zip [] xs :=: [])

prop_47 a
  = prove (height (mirror a) :=: height a)

prop_48 xs
  = given (xs =:= [] :=: False)
  $ prove (init xs ++ [last xs] :=: xs)

prop_49 xs ys
  = prove (init (xs ++ ys) :=: initConcat xs ys)

prop_50 xs
  = prove (init xs :=: take (len xs - S Z) xs)

prop_51 xs x
  = prove (init (xs ++ [x]) :=: xs)

prop_52 n xs
  = prove (count n xs :=: count n (rev xs))

prop_53 n xs
  = prove (count n xs :=: count n (sort xs))

prop_54 (n :: Nat) m
  = prove ((m + n) - n :=: m)

prop_55 n xs ys
  = prove (drop n (xs ++ ys) :=: drop n xs ++ drop (n - len xs) ys)

prop_56 n m xs
  = prove (drop n (drop m xs) :=: drop (n + m) xs)

prop_57 n m xs
  = prove (drop n (take m xs) :=: take (m - n) (drop n xs))

prop_58 n xs ys
  = prove (drop n (zip xs ys) :=: zip (drop n xs) (drop n ys))

prop_59 xs ys
  = givenBool (ys =:= [])
  $ prove (last (xs ++ ys) :=: last xs)

prop_60 xs ys
  = given (ys =:= [] :=: False)
  $ prove (last (xs ++ ys) :=: last ys)

prop_61 xs ys
  = prove (last (xs ++ ys) :=: lastOfTwo xs ys)

prop_62 xs x
  = given (xs =:= [] :=: False)
  $ prove (last (x:xs) :=: last xs)

prop_63 n xs
  = givenBool (n < len xs)
  $ prove (last (drop n xs) :=: last xs)

prop_64 x xs
  = prove (last (xs ++ [x]) :=: x)

prop_65 (i :: Nat) m =
  proveBool (i < S (m + i))

prop_66 p xs
  = proveBool (len (filter p xs) <= len xs)

prop_67 xs
  = prove (len (init xs) :=: len xs - S Z)

prop_68 n xs
  = proveBool (len (delete n xs) <= len xs)

prop_69 (n :: Nat) m
  = proveBool (n <= (m + n))

prop_70 m n
  = givenBool (m <= n)
  $ proveBool (m <= S n)

prop_71 x y xs
  = given (x == y :=: False)
  $ prove (elem x (ins y xs) :=: elem x xs)

prop_72 i xs
  = prove (rev (drop i xs) :=: take (len xs - i) (rev xs))

prop_73 p xs
  = prove (rev (filter p xs) :=: filter p (rev xs))

prop_74 i xs
  = prove (rev (take i xs) :=: drop (len xs - i) (rev xs))

prop_75 n m xs
  = prove (count n xs + count n [m] :=: count n (m : xs))

prop_76 n m xs
  = given (n == m :=: False)
  $ prove (count n (xs ++ [m]) :=: count n xs)

prop_77 x xs
  = givenBool (sorted xs)
  $ proveBool (sorted (insort x xs))

prop_78 xs
  = proveBool (sorted (sort xs))

prop_79 (m :: Nat) n k
  = prove ((S m - n) - S k :=: (m - n) - k)

prop_80 n xs ys
  = prove (take n (xs ++ ys) :=: take n xs ++ take (n - len xs) ys)

prop_81 n m xs ys
  = prove (take n (drop m xs) :=: drop m (take (n + m) xs))

prop_82 n xs ys
  = prove (take n (zip xs ys) :=: zip (take n xs) (take n ys))

prop_83 xs ys zs
  = prove (zip (xs ++ ys) zs :=:
           zip xs (take (len xs) zs) ++ zip ys (drop (len xs) zs))

prop_84 xs ys zs
  = prove (zip xs (ys ++ zs) :=:
           zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs)

prop_85 xs ys
  = prove (zip (rev xs) (rev ys) :=: rev (zip xs ys))

