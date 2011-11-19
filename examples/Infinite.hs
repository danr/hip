-- Properties of infinite objects
module Infinity where

import Prelude (Bool(..))

infix 1 =:=
type Prop a = a
prove :: a -> Prop a
prove = prove
proveBool :: a -> Prop Bool
proveBool = proveBool
(=:=) :: a -> a -> a
(=:=) = (=:=)


(.) :: (b -> c) -> (a -> b) -> a -> c
(f . g) x = f (g x)

id x = x

map :: (a -> b) -> [a] -> [b]
map f []       = []
map f (x : xs) = f x : map f xs


concat :: [[a]] -> [a]
concat [] = []
concat ([]:xss)     = concat xss
concat ((x:xs):xss) = x : concat (xs:xss)

iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) | p x = x : (filter p xs)
filter p (x:xs) = filter p xs

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



prop_map_iterate :: (a -> a) -> a -> Prop [a]
prop_map_iterate f x = prove (map f (iterate f x) =:= iterate f (f x))

prop_filter_iterate :: (a -> Bool) -> (a -> a) -> a -> Prop [a]
prop_filter_iterate p f x = prove (filter p    (iterate f (f x)) =:=
                                   filter (p . f) (iterate f x))


prop_repeat_iterate :: a -> Prop [a]
prop_repeat_iterate x = prove (repeat x =:= iterate id x)

prop_repeat_cycle_singleton :: a -> Prop [a]
prop_repeat_cycle_singleton x = prove (repeat x =:= cycle [x])

prop_concat_repeat_cycle :: [a] -> Prop [a]
prop_concat_repeat_cycle xs = prove (concat (repeat xs) =:= cycle xs)

prop_tail_repeat :: a -> Prop [a]
prop_tail_repeat x = prove (repeat x =:= tail (repeat x))

data Tree a = Empty | Branch (Tree a) a (Tree a)

iterTree :: (a -> a) -> (a -> a) -> a -> Tree a
iterTree f g x = Branch (iterTree f g (f x)) x (iterTree f g (g x))

fmap :: (a -> b) -> Tree a -> Tree b
fmap f Empty = Empty
fmap f (Branch l x r) = Branch (fmap f l) (f x) (fmap f r)

repeatTree :: a -> Tree a
repeatTree x = Branch (repeatTree x) x (repeatTree x)

mirror :: Tree a -> Tree a
mirror (Branch l x r) = Branch (mirror l) x (mirror r)
mirror Empty          = Empty

traverse :: Tree a -> [a]
traverse (Branch l x r) = traverse l ++ [x] ++ traverse r
traverse Empty          = []

toList :: Tree a -> [a]
toList (Branch l x r) = x : toList l ++ toList r
toList Empty          = []

reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = xs ++ [x]

prop_fmap_iterate :: (a -> a) -> a -> Prop (Tree a)
prop_fmap_iterate f x = prove (fmap f (iterTree f f x) =:=
                               iterTree f f (f x))

prop_fmap_comp :: (b -> c) -> (a -> b) -> Tree a -> Prop (Tree c)
prop_fmap_comp f g t = prove (fmap (f . g) t =:= fmap f (fmap g t))

prop_fmap_left :: (a -> b) -> Tree a -> Prop (Tree b)
prop_fmap_left f t = prove (fmap (id . f) t =:= fmap f t)

prop_fmap_right :: (a -> b) -> Tree a -> Prop (Tree b)
prop_fmap_right f t = prove (fmap (f . id) t =:= fmap f t)

prop_fmap_id :: (b -> c) -> (a -> b) -> Tree a -> Prop (Tree c)
prop_fmap_id t = prove (fmap id t =:= t)
n
prop_mirror_involutive :: Tree a -> Prop (Tree a)
prop_mirror_involutive t = prove (mirror (mirror t) =:= t)

prop_mirror_iterate :: a -> (a -> a) -> (a -> a) -> Prop (Tree a)
prop_mirror_iterate x f g = prove (mirror (iterTree f g x) =:= iterTree g f x)

prop_fmap_map_traverse :: Tree a -> (a -> b) -> Prop [b]
prop_fmap_map_traverse t f = prove (map f (traverse t) =:= traverse (fmap f t))

prop_fmap_map_toList :: Tree a -> (a -> b) -> Prop [b]
prop_fmap_map_toList t f = prove (map f (toList t) =:= toList (fmap f t))

prop_mirror_traverse_rev :: Tree a -> Prop [a]
prop_mirror_traverse_rev t = prove (reverse (traverse t) =:= traverse (mirror t))

