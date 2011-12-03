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

-- Sometimes, Malin and Mikael help me with names of properties

prop_malins_identity :: b -> a -> Prop a
prop_malins_identity x y = prove (const id x y =:= flip const x y)

prop_malins_identity' :: Prop (a -> b -> b)
prop_malins_identity' = prove (const id =:= flip const)

prop_mikaels_identity :: (a -> b) -> a -> Prop b
prop_mikaels_identity f x = prove (id f x =:= f x)

prop_dans_identity :: a -> a -> Prop a
prop_dans_identity x y = prove (const x y =:= id x)

prop_dans_nonidentity :: a -> a -> Prop a
prop_dans_nonidentity x y = prove (const y x =:= id x)

prop_nonidentity :: a -> Prop (a -> a)
prop_nonidentity x = prove (const x =:= id)

uncurry :: (a -> b -> c) -> (a,b) -> c
uncurry f (a,b) = f a b

curry :: ((a,b) -> c) -> a -> b -> c
curry f a b = f (a,b)

(f . g) x = f (g x)

prop_curry_uncurry :: Prop ((a -> b -> c) -> a -> b -> c)
prop_curry_uncurry = prove (id =:= curry . uncurry)

prop_uncurry_curry :: Prop (((a,b) -> c) -> (a,b) -> c)
prop_uncurry_curry = prove (id =:= uncurry . curry)

f ... g = \x -> f (g x)

prop_comp_equal :: Prop ((b -> c) -> (a -> b) -> a -> c)
prop_comp_equal = prove ((.) =:= (...))

prop_comp_assocl :: (c -> d) -> (b -> c) -> (a -> b) -> Prop (a -> d)
prop_comp_assocl f g h = prove (((f . g) . h) =:= (f . (g . h)))

prop_comp_assoc :: (c -> d) -> (b -> c) -> (a -> b) -> Prop (a -> d)
prop_comp_assoc f g h = prove (((f ... g) ... h) =:= (f ... (g ... h)))