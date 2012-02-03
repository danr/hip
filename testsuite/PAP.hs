module PAP where

import AutoPrelude
import Prelude ()

data Nat = Z | S Nat

Z     + y = y
(S x) + y = S (x + y)

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

one = S Z

-- (+ one) and (one +) is not equal here. (of course) One is a finite
-- theorem and the other is a theorem. The two-depth structural
-- induction finds the finite theorem, but the simple induction fails
-- to find this as it is not a theorem with : if the natural number is
-- not total.
incr = map (one +)

incrrec (x:xs) = S x : incrrec xs
incrrec []     = []

prop_equal :: [Nat] -> Prop [Nat]
prop_equal xs = incrrec xs =:= incr xs