module ProductiveUseOfFailure where

import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),undefined,Int)
import AutoPrelude

otherwise = True

data Nat = S Nat | Z
  deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in  (nats !!) `fmap` choose (0,7)

True  && x = x
False && _ = False

False || x = x
True  || x = True

True  <=> True  = True
False <=> False = True
_     <=> _     = False

True --> False = False
_    --> _     = True

infixl 2 -->

infix 3 <=>

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)

-- revflat and qrevflat is mentioned in the properties but I do not
-- know what it is
revflat = rev
qrevflat = qrev

double :: Nat -> Nat
double Z = Z
double (S x) = S (S (double x))

even :: Nat -> Bool
even Z = True
even (S Z) = False
even (S (S x)) = even x

half :: Nat -> Nat
half Z = Z
half (S Z) = Z
half (S (S x)) = S (half x)

mult :: Nat -> Nat -> Nat -> Nat
mult Z     _ acc = acc
mult (S x) y acc = mult x y (y + acc)

fac :: Nat -> Nat
fac Z = S Z
fac (S x) = S x * fac x

qfac :: Nat -> Nat -> Nat
qfac Z     acc = acc
qfac (S x) acc = qfac x (S x * acc)

exp :: Nat -> Nat -> Nat
exp _ Z     = S Z
exp x (S n) = x * exp x n

qexp :: Nat -> Nat -> Nat -> Nat
qexp x Z     acc = acc
qexp x (S n) acc = qexp x n (x * acc)

(+),(*) :: Nat -> Nat -> Nat
Z     + y = y
(S x) + y = S (x + y)

Z     * _ = Z
(S x) * y = y + (x * y)

rotate :: Nat -> [a] -> [a]
rotate Z     xs     = xs
rotate _     []     = []
rotate (S n) (x:xs) = rotate n (xs ++ [x])

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) = n == x || elem n xs

subset :: [Nat] -> [Nat] -> Bool
subset []     ys = True
subset (x:xs) ys = x `elem` xs && subset xs ys

intersect,union :: [Nat] -> [Nat] -> [Nat]
(x:xs) `intersect` ys | x `elem` ys = x:(xs `intersect` ys)
                      | otherwise   = xs `intersect` ys
[]     `intersect` ys = []

union (x:xs) ys | x `elem` ys = union xs ys
                | otherwise   = x:(union xs ys)
union []     ys = ys

isort :: [Nat] -> [Nat]
isort [] = []
isort (x:xs) = insert x (isort xs)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insert n xs)

count :: Nat -> [Nat] -> Nat
count n (x:xs) | n == x = S (count n xs)
               | otherwise = count n xs
count n [] = Z

(==),(/=) :: Nat -> Nat -> Bool
Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

x /= y = not (x == y)

not True  = False
not False = True

listEq :: [Nat] -> [Nat] -> Bool
listEq []     []     = True
listEq (x:xs) (y:ys) = x == y && (xs `listEq` ys)

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

sorted :: [Nat] -> Bool
sorted (x:y:xs) = x <= y && sorted (y:xs)
sorted _        = True

zero = Z
one  = S Z

prop_T1 :: Nat -> Prop Nat
prop_T1 x       = double x =:= x + x

prop_T2 :: [a] -> [a] -> Prop Nat
prop_T2 x y     = length (x ++ y ) =:= length (y ++ x)

prop_T3 :: [a] -> [a] -> Prop Nat
prop_T3 x y     = length (x ++ y ) =:= length (y ) + length x

prop_T4 :: [a] -> Prop Nat
prop_T4 x       = length (x ++ x) =:= double (length x)

prop_T5 :: [a] -> Prop Nat
prop_T5 x       = length (rev x) =:= length x

prop_T6 :: [a] -> [a] -> Prop Nat
prop_T6 x y     = length (rev (x ++ y )) =:= length x + length y

prop_T7 :: [a] -> [a] -> Prop Nat
prop_T7 x y     = length (qrev x y) =:= length x + length y

prop_T8 :: Nat -> Nat -> [a] -> Prop [a]
prop_T8 x y z   = drop x (drop y z) =:= drop y (drop x z)

prop_T9 :: Nat -> Nat -> [a] -> Nat -> Prop [a]
prop_T9 x y z w = drop w (drop x (drop y z)) =:= drop y (drop x (drop w z))

prop_T10 :: [a] -> Prop [a]
prop_T10 x      = rev (rev x) =:= x

prop_T11 :: [a] -> [a] -> Prop [a]
prop_T11 x y    = rev (rev x ++ rev y) =:= y ++ x

prop_T12 :: [a] -> [a] -> Prop [a]
prop_T12 x y    = qrev x y =:= rev x ++ y

prop_T13 :: Nat -> Prop Nat
prop_T13 x      = half (x + x) =:= x

prop_T14 :: [Nat] -> Prop Bool
prop_T14 x      = proveBool (sorted (isort x))

prop_T15 :: Nat -> Prop Nat
prop_T15 x      = x + S x =:= S (x + x)

prop_T16 :: Nat -> Prop Bool
prop_T16 x      = proveBool (even (x + x))

prop_T17 :: [a] -> [a] -> Prop [a]
prop_T17 x y    = rev (rev (x ++ y)) =:= rev (rev x) ++ rev (rev y)

prop_T18 :: [a] -> [a] -> Prop [a]
prop_T18 x y    = rev (rev x ++ y) =:= rev y ++ x

prop_T19 :: [a] -> [a] -> Prop [a]
prop_T19 x y    = rev (rev x) ++ y =:= rev (rev (x ++ y))

prop_T20 :: [a] -> Prop Bool
prop_T20 x      = proveBool (even (length (x ++ x)))

prop_T21 :: [a] -> [a] -> Prop [a]
prop_T21 x y    = rotate (length x) (x ++ y) =:= y ++ x

prop_T22 :: [a] -> [a] -> Prop Bool
prop_T22 x y    = proveBool (even (length (x ++ y)) <=> even (length (y ++ x)))

prop_T23 :: [a] -> [a] -> Prop Nat
prop_T23 x y    = half (length (x ++ y)) =:= half (length (y ++ x))

prop_T24 :: Nat -> Nat -> Bool
prop_T24 x y    = even (x + y) <=> even (y + x)

prop_T25 :: [a] -> [a] -> Prop Bool
prop_T25 x y    = proveBool (even (length (x ++ y)) <=> even (length y + length x))

prop_T26 :: Nat -> Nat -> Prop Nat
prop_T26 x y    = half (x + y) =:= half (y + x)

prop_T27 :: [a] -> Prop [a]
prop_T27 x      = rev x =:= qrev x []

prop_T28 :: [a] -> Prop [a]
prop_T28 x      = revflat x =:= qrevflat x []

prop_T29 :: [a] -> Prop [a]
prop_T29 x      = rev (qrev x []) =:= x

prop_T30 :: [a] -> Prop [a]
prop_T30 x      = rev (rev x ++ []) =:= x

prop_T31 :: [a] -> Prop [a]
prop_T31 x      = qrev (qrev x []) [] =:= x

prop_T32 :: [a] -> Prop [a]
prop_T32 x      = rotate (length x) x =:= x

prop_T33 :: Nat -> Prop Nat
prop_T33 x      = fac x =:= qfac x one

prop_T34 :: Nat -> Nat -> Prop Nat
prop_T34 x y    = x * y =:= mult x y zero

prop_T35 :: Nat -> Nat -> Prop Nat
prop_T35 x y    = exp x y =:= qexp x y one

prop_T36 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T36 x y z  = proveBool (x `elem` y --> x `elem` (y ++ z))

prop_T37 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T37 x y z  = proveBool (x `elem` z --> x `elem` (y ++ z))

prop_T38 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T38 x y z  = proveBool ((x `elem` y) && (x `elem` z) --> x `elem` (y ++ z))

prop_T39 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_T39 x y z  = proveBool (x `elem` drop y z --> x `elem` z)

prop_T40 :: [Nat] -> [Nat] -> Prop Bool
prop_T40 x y    = proveBool (x `subset` y --> ((x `union` y) `listEq` y))

prop_T41 :: [Nat] -> [Nat] -> Prop Bool
prop_T41 x y    = proveBool (x `subset` y --> ((x `intersect` y) `listEq` x))

prop_T42 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T42 x y z  = proveBool (x `elem` y --> x `elem` (y `union` z))

prop_T43 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T43 x y z  = proveBool (x `elem` y --> x `elem` (z `union` y))

prop_T44 :: Nat -> [Nat] -> [Nat] -> Prop Bool
prop_T44 x y z  = proveBool ((x `elem` y) && (x `elem` z) --> (x `elem` (y `intersect` z)))

prop_T45 :: Nat -> [Nat] -> Prop Bool
prop_T45 x y    = proveBool (x `elem` insert x y)

prop_T46 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_T46 x y z  = proveBool (x == y --> (x `elem` insert y z) <=> True)

prop_T47 :: Nat -> Nat -> [Nat] -> Prop Bool
prop_T47 x y z  = proveBool (x /= y --> (x `elem` insert y z) <=> x `elem` z)

prop_T48 :: [Nat] -> Prop Nat
prop_T48 x      = length (isort x) =:= length x

prop_T49 :: Nat -> [Nat] -> Prop Bool
prop_T49 x y    = proveBool (x `elem` isort y --> x `elem` y)

prop_T50 :: Nat -> [Nat] -> Prop Nat
prop_T50 x y    = count x (isort y) =:= count x y

main = do
  quickCheck (printTestCase "prop_T1" (prop_T1 :: Nat -> Prop Nat))
  quickCheck (printTestCase "prop_T2" (prop_T2 :: [Int] -> [Int] -> Prop Nat))
  quickCheck (printTestCase "prop_T3" (prop_T3 :: [Int] -> [Int] -> Prop Nat))
  quickCheck (printTestCase "prop_T4" (prop_T4 :: [Int] -> Prop Nat))
  quickCheck (printTestCase "prop_T5" (prop_T5 :: [Int] -> Prop Nat))
  quickCheck (printTestCase "prop_T6" (prop_T6 :: [Int] -> [Int] -> Prop Nat))
  quickCheck (printTestCase "prop_T7" (prop_T7 :: [Int] -> [Int] -> Prop Nat))
  quickCheck (printTestCase "prop_T8" (prop_T8 :: Nat -> Nat -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T9" (prop_T9 :: Nat -> Nat -> [Int] -> Nat -> Prop [Int]))
  quickCheck (printTestCase "prop_T10" (prop_T10 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T11" (prop_T11 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T12" (prop_T12 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T13" (prop_T13 :: Nat -> Prop Nat))
  quickCheck (printTestCase "prop_T14" (prop_T14 :: [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T15" (prop_T15 :: Nat -> Prop Nat))
  quickCheck (printTestCase "prop_T16" (prop_T16 :: Nat -> Prop Bool))
  quickCheck (printTestCase "prop_T17" (prop_T17 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T18" (prop_T18 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T19" (prop_T19 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T20" (prop_T20 :: [Int] -> Prop Bool))
  quickCheck (printTestCase "prop_T21" (prop_T21 :: [Int] -> [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T22" (prop_T22 :: [Int] -> [Int] -> Prop Bool))
  quickCheck (printTestCase "prop_T23" (prop_T23 :: [Int] -> [Int] -> Prop Nat))
  quickCheck (printTestCase "prop_T24" (prop_T24 :: Nat -> Nat -> Bool))
  quickCheck (printTestCase "prop_T25" (prop_T25 :: [Int] -> [Int] -> Prop Bool))
  quickCheck (printTestCase "prop_T26" (prop_T26 :: Nat -> Nat -> Prop Nat))
  quickCheck (printTestCase "prop_T27" (prop_T27 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T28" (prop_T28 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T29" (prop_T29 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T30" (prop_T30 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T31" (prop_T31 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T32" (prop_T32 :: [Int] -> Prop [Int]))
  quickCheck (printTestCase "prop_T33" (prop_T33 :: Nat -> Prop Nat))
  quickCheck (printTestCase "prop_T34" (prop_T34 :: Nat -> Nat -> Prop Nat))
  quickCheck (printTestCase "prop_T35" (prop_T35 :: Nat -> Nat -> Prop Nat))
  quickCheck (printTestCase "prop_T36" (prop_T36 :: Nat -> [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T37" (prop_T37 :: Nat -> [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T38" (prop_T38 :: Nat -> [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T39" (prop_T39 :: Nat -> Nat -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T40" (prop_T40 :: [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T41" (prop_T41 :: [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T42" (prop_T42 :: Nat -> [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T43" (prop_T43 :: Nat -> [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T44" (prop_T44 :: Nat -> [Nat] -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T45" (prop_T45 :: Nat -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T46" (prop_T46 :: Nat -> Nat -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T47" (prop_T47 :: Nat -> Nat -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T48" (prop_T48 :: [Nat] -> Prop Nat))
  quickCheck (printTestCase "prop_T49" (prop_T49 :: Nat -> [Nat] -> Prop Bool))
  quickCheck (printTestCase "prop_T50" (prop_T50 :: Nat -> [Nat] -> Prop Nat))
