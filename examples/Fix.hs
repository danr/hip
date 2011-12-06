module Fix where

import AutoPrelude
import Prelude (fmap,(!!),Eq,Show,Bool(..),(.),iterate)

data Nat = S Nat | Z deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary = sized (fmap (nats !!) . choose . (,) 0)
    where nats = iterate S Z

not True = False
not False = True

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

fst (x,y) = x
snd (x,y) = y

uncurry f t = f (fst t) (snd t)

fix f = f (fix f)

evenFix,oddFix :: Nat -> Bool
fixed = fix (\t -> (uncurry evenFixMe t,uncurry oddFixMe t))
evenFix = fst fixed
oddFix  = snd fixed

prop_even,prop_odd :: Nat -> Prop Bool
prop_even x = even x =:= evenFix x
prop_odd  x = odd x  =:= oddFix x

-- Single fix -----------------------------------------------------------------
evenSinglFixMe :: (Nat -> Bool) -> Nat -> Bool
evenSinglFixMe evenUnRec Z     = True
evenSinglFixMe evenUnRec (S x) = not (oddWhere x)
  where
    oddWhere Z     = True
    oddWhere (S x) = not (evenUnRec x)

evenSingl :: Nat -> Bool
evenSingl = fix evenSinglFixMe

prop_evenSingl :: Nat -> Prop Bool
prop_evenSingl x = evenSingl x =:= even x

prop_evenSinglFix :: Nat -> Prop Bool
prop_evenSinglFix x = evenSingl x =:= evenFix x
