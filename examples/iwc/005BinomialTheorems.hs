{-# LANGUAGE FlexibleInstances #-}
-- http://www.csc.liv.ac.uk/~lad/research/challenges/IWC005a.txt

import Test.QuickCheck

data Nat = S Nat | Z
  deriving (Eq,Show)

plus x Z     = x
plus x (S y) = S (plus x y)

times x Z     = Z
times x (S y) = (x `times` y) `plus` x

choose' x     Z     = S Z
choose' Z     (S y) = Z
choose' (S x) (S y) = choose' x (S y) `plus` choose' x y

exp' x Z     = Z
exp' x (S y) = exp' x y `times` x

lt x     Z     = False
lt Z     y     = True
lt (S x) (S y) = lt x y

sum' :: Nat -> Nat -> (Nat -> Nat) -> Nat
sum' x Z     f = f Z
sum' x (S y) f | S y `lt` x = Z
               | otherwise  = f (S y) `plus` sum' x y f

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in sized $ \s -> do
          x <- choose (0,s)
          return (nats !! x)

instance CoArbitrary Nat where
  coarbitrary Z     = variant 0
  coarbitrary (S n) = variant (-1) . coarbitrary n

instance Show (Nat -> Nat) where
  show f = show [ (x,f x) | x <- take 10 (iterate S Z) ]

prop_binomialTheorems :: Nat -> Nat -> Bool
prop_binomialTheorems x n = exp' (S x) n == sum' Z n (\i -> choose' n i `times` exp' x i)

minus n Z = n
minus (S n) (S k) = minus n k
minus Z k = Z

prop_chooseLemma :: Nat -> Nat -> Property
prop_chooseLemma n k = k `lt` n ==> choose' n k == choose' n (n `minus` k)

prop_sumLemma :: Nat -> Nat -> (Nat -> Nat) -> (Nat -> Nat) -> Bool
prop_sumLemma n m f g = sum' n m (\i -> f i `plus` g i) == sum' n m f `plus` sum' n m g

prop_sumLemma2 :: Nat -> Nat -> Nat -> (Nat -> Nat) -> Bool
prop_sumLemma2 n m t f = sum' n m (\i -> t `times` f i) == t `times` sum' n m f


