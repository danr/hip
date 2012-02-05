module Trees where

import AutoPrelude
import Prelude (Eq,Show)

data Tree a = Bin (Tree a) (Tree a)
            | Leaf a
  deriving(Eq,Show)

return :: a -> Tree a
return = Leaf

(>>=) :: Tree a -> (a -> Tree b) -> Tree b
Bin l r >>= f = Bin (l >>= f) (r >>= f)
Leaf x  >>= f = f x

prop_return_right :: Tree a -> Prop (Tree a)
prop_return_right t = (t >>= return) =:= t

prop_return_left :: (a -> Tree b) -> a -> Prop (Tree b)
prop_return_left f x = (return x >>= f) =:= f x

prop_assoc :: Tree a -> (a -> Tree b) -> (b -> Tree c) -> Prop (Tree c)
prop_assoc t f g = ((t >>= f) >>= g) =:= (t >>= (\x -> f x >>= g))

