module Ordinals where

import AutoPrelude
import qualified Prelude as P

data Nat = Z | S Nat deriving (P.Show)

Z     + y = y
(S x) + y = S (x + y)

Z     * _ = Z
(S x) * y = y + (x * y)

data Ord = Zero | Suc Ord | Lim (Nat -> Ord)

(++) :: Ord -> Ord -> Ord
Zero  ++ y = y
Suc x ++ y = Suc (x ++ y)
Lim f ++ y = Lim (\n -> f n ++ y)

(**) :: Ord -> Ord -> Ord
Zero  ** y = Zero
Suc x ** y = y ++ (x ** y)
Lim f ** y = Lim (\n -> f n ** y)

prop_assoc_plus :: Ord -> Ord -> Ord -> Prop Ord
prop_assoc_plus x y z = x ++ (y ++ z) =:= (x ++ y) ++ z

prop_assoc_mul :: Ord -> Ord -> Ord -> Prop Ord
prop_assoc_mul x y z = x ** (y ** z) =:= (x ** y) ** z

prop_right_identity_plus :: Ord -> Prop Ord
prop_right_identity_plus x = x ++ Zero =:= x

prop_left_identity_plus :: Ord -> Prop Ord
prop_left_identity_plus x = Zero ++ x =:= x

prop_right_identity_mul :: Ord -> Prop Ord
prop_right_identity_mul x = x ** Suc Zero =:= x

prop_left_identity_mul :: Ord -> Prop Ord
prop_left_identity_mul x = Suc Zero ** x =:= x

prop_add_comm :: Nat -> Nat -> Prop Nat
prop_add_comm x y = x ++ y =:= y ++ x

prop_mul_lemma :: Nat -> Nat -> Prop Nat
prop_mul_lemma m n = m ** S n =:= m ++ m ** n

prop_mul_comm :: Nat -> Nat -> Prop Nat
prop_mul_comm x y = x ** y =:= y ** x

prop_left_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_left_distrib x y z = x ** (y ++ z) =:= (x ** y) ++ (x ** z)

prop_right_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_right_distrib x y z = (x ++ y) ** z =:= (x ** z) ++ (y ** z)


{-
finite :: Nat -> Ord
finite Z     = Zero
finite (S n) = Suc (finite n)

omega :: Ord
omega = Lim finite


instance Show Ord where
  show Zero = "Zero"
  show (Suc n) = "Succ (" P.++ show n P.++ ")"
  show (Lim f) = "Lim (" P.++ P.unwords
                     [ show (f n)
                     | n <- [Z, S Z, S (S Z), S (S (S Z))]
                     ] P.++ ")"
-}