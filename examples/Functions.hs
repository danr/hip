module Functions where

import Prelude ()

infix 1 =:=
type Prop a = a
prove :: a -> Prop a
prove = prove
(=:=) :: a -> a -> a
(=:=) = (=:=)

const x y = x
flip f x y = f y x
id x = x

prop_malins_identity :: b -> a -> Prop a
prop_malins_identity x y = prove (const id x y =:= flip const x y)

prop_mikaels_identity :: (a -> b) -> a -> Prop b
prop_mikaels_identity f x = prove (id f x =:= f x)

prop_dans_nonidentity :: a -> a -> Prop a
prop_dans_nonidentity x y = prove (const x y =:= id x)

uncurry :: (a -> b -> c) -> (a,b) -> c
uncurry f (a,b) = f a b

curry :: ((a,b) -> c) -> a -> b -> c
curry f a b = f (a,b)

(f . g) x = f (g x)

prop_curry_uncurry :: Prop ((a -> b -> c) -> a -> b -> c)
prop_curry_uncurry = prove (id =:= curry . uncurry)

prop_uncurry_curry :: Prop (((a,b) -> c) -> (a,b) -> c)
prop_uncurry_curry = prove (id =:= uncurry . curry)