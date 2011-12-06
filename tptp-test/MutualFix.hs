{-# LANGUAGE TupleSections #-}
module MutualFix where

import Prelude hiding (even,odd)
import Data.Function
import Control.Arrow
import Control.Applicative
import Test.QuickCheck

data Nat = S Nat | Z deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary = sized (fmap (nats !!) . choose . (0,))
    where nats = iterate S Z

even :: Nat -> Bool
even Z     = True
even (S x) = not (odd x)

odd :: Nat -> Bool
odd Z     = True
odd (S x) = not (even x)

evenFixMe :: (Nat -> Bool) -> (Nat -> Bool) -> Nat -> Bool
evenFixMe evenUnRec oddUnRec Z     = True
evenFixMe evenUnRec oddUnRec (S x) = not (oddUnRec x)

oddFixMe :: (Nat -> Bool) -> (Nat -> Bool) -> Nat -> Bool
oddFixMe evenUnRec oddUnRec Z     = True
oddFixMe evenUnRec oddUnRec (S x) = not (evenUnRec x)

evenFix,oddFix :: Nat -> Bool
(evenFix,oddFix) = fix (uncurry evenFixMe &&& uncurry oddFixMe)

prop_even,prop_odd :: Nat -> Bool
prop_even = (==) <$> even <*> evenFix
prop_odd  = (==) <$> odd  <*> oddFix

