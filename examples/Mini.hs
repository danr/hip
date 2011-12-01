-- Some examples of Nats and Lists

import Prelude ()

type Prop a = a
prove = prove
proveBool = proveBool
(=:=) = (=:=)
otherwise = True
infix 1 =:=

Z     + y = y
(S x) + y = S (x + y)

Z     * _ = Z
(S x) * y = y + (x * y)

data Nat = Z | S Nat

-- Disprove
prop_zero_is_one :: Prop Nat
prop_zero_is_one = prove (Z =:= S Z)

-- Induction on x. Also holds in the presence of bottoms
prop_assoc_plus :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_plus x y z
  = prove (x + (y + z) =:= (x + y) + z)

-- Needs assoc plus as lemma
prop_assoc_mul :: Nat -> Nat -> Nat -> Prop Nat
prop_assoc_mul x y z
  = prove (x * (y * z) =:= (x * y) * z)

-- True by definition
prop_right_identity_plus :: Nat -> Prop Nat
prop_right_identity_plus x
  = prove (x + Z =:= x)

-- Induction on x
prop_left_identity_plus :: Nat -> Prop Nat
prop_left_identity_plus x
  = prove (Z + x =:= x)

-- Lemma for commutativity of addition
prop_movesuc :: Nat -> Nat -> Prop Nat
prop_movesuc x y = prove (S x + y =:= x + S y)

-- Provable for total elements by induction on both variables,
-- symmetrically, or with movesuc lemma
prop_add_comm :: Nat -> Nat -> Prop Nat
prop_add_comm x y
  = prove (x + y =:= y + x)

prop_left_distrib :: Nat -> Nat -> Nat -> Prop Nat
prop_left_distrib x y z
  = prove (x * (y + z) =:= (x * y) + (x * z))

map :: (a -> b) -> [a] -> [b]
map f []       = []
map f (x : xs) = f x : map f xs

iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

repeat :: a -> [a]
repeat x = x : repeat x

cycle :: [a] -> [a]
cycle xs = xs ++ cycle xs

tail :: [a] -> [a]
tail [x]    = []
tail (x:xs) = x:tail xs

id :: a -> a
id x = x

prop_map_iterate :: (a -> a) -> a -> Prop [a]
prop_map_iterate f x = prove (map f (iterate f x) =:= iterate f (f x))

prop_repeat_iterate :: a -> Prop [a]
prop_repeat_iterate x = prove (repeat x =:= iterate id x)

prop_repeat_cycle_singleton :: a -> Prop [a]
prop_repeat_cycle_singleton x = prove (repeat x =:= cycle [x])

prop_tail_repeat :: a -> Prop [a]
prop_tail_repeat x = prove (repeat x =:= tail (repeat x))
