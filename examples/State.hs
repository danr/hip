
-- run with hip State.hs --enable-seq
-- and preferably with --provers=z, to enable z3

module State where

import HipPrelude
import Prelude ()

-- Strict uncurry
uncurry' f (x,y) = f x y

-- Lazy uncurry
uncurry f t = f (fst t) (snd t)

fst (x,y) = x
snd (x,y) = y

f . g = \x -> f (g x)

-- Strict bind
m >>= f = uncurry f . m

return x = \s -> (x,s)

prop_return_left :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left m = m >>= return =:= m

prop_return_right :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right f a = return a >>= f =:= f a

prop_assoc :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc m f g = (m >>= f) >>= g =:= m >>= (\x -> f x >>= g)
