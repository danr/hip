-- Properties of Natural numbers, with swap-definition of plus and
-- multiplication
module Nat where

import Prelude ()

type Prop a = a
prove = prove
proveBool = proveBool
(=:=) = (=:=)
infix 1 =:=

data Nat = Z | S Nat

Z   + y = y
S x + y = S (y + x)

Z   * _ = Z
S x * y = y + (y * x)

Z   - _   = Z
x   - Z   = x
S x - S y = x - y

Z   <= _   = True
_   <= Z   = False
S x <= S y = x <= y

_   < Z   = False
Z   < _   = True
S x < S y = x < y

-- Only properties directly or indirectly regarding +

prop_assoc_plus :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_plus x y z
  = prove (x + (y + z) =:= (x + y) + z)

prop_assoc_mul :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_mul x y z
  = prove (x * (y * z) =:= (x * y) * z)

prop_right_identity_plus :: Nat -> Prop Nat
prop_right_identity_plus x
  = prove (x + Z =:= x)

prop_left_identity_plus :: Nat -> Prop Nat
prop_left_identity_plus x
  = prove (Z + x =:= x)

prop_right_identity_mul :: Nat -> Prop Nat
prop_right_identity_mul x
  = prove (x * S Z =:= x)

prop_left_identity_mul :: Nat -> Prop Nat
prop_left_identity_mul x
  = prove (S Z * x =:= x)

prop_add_comm :: Nat -> Nat -> Prop Nat
prop_add_comm x y
  = prove (x + y =:= y + x)

prop_mul_comm :: Nat -> Nat -> Prop Nat
prop_mul_comm x y
  = prove (x * y =:= y * x)

prop_left_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_left_distrib x y z
  = prove (x * (y + z) =:= (x * y) + (x * z))

prop_right_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_right_distrib x y z
  = prove ((x + y) * z =:= (x * z) + (y * z))

prop_idem_plus :: Nat -> Prop Nat
prop_idem_plus x
  = prove (x + x =:= x)

prop_idem_mul :: Nat -> Prop Nat
prop_idem_mul x
  = prove (x * x =:= x)

prop_minus_zeroish :: Nat -> Nat -> Prop Nat
prop_minus_zeroish n m
  = prove (n - (n + m) =:= Z)

prop_minus_absorbish  :: Nat -> Nat -> Prop Nat
prop_minus_absorbish n m
  = prove ((n + m) - n =:= m)

prop_minus_distribish :: Nat -> Nat -> Nat -> Prop Nat
prop_minus_distribish k m n
  = prove ((k + m) - (k + n) =:= m - n)

prop_le_succ_plus :: Nat -> Nat -> Prop Bool
prop_le_succ_plus i m
  = proveBool (i < S (i + m))

prop_le_plus :: Nat -> Nat -> Prop Bool
prop_le_plus n m
  = proveBool (n <= (n + m))

prop_le_plus_sym :: Nat -> Nat -> Prop Bool
prop_le_plus_sym n m
  = proveBool (n <= (m + n))

prop_minus_plus :: Nat -> Nat -> Prop Nat
prop_minus_plus n m
  = prove ((m + n) - n =:= m)

prop_lt_suc  :: Nat -> Nat -> Prop Bool
prop_lt_suc i m
  = proveBool (i < S (m + i))
