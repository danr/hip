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

fst (x,y) = x
snd (x,y) = y

uncurry' :: (a -> b -> c) -> (a,b) -> c
uncurry' f t = f (fst t) (snd t)

prop_uncurry_equal :: Prop ((a -> b -> c) -> (a,b) -> c)
prop_uncurry_equal = prove (uncurry =:= uncurry')

prop_uncurry_f_equal :: (a -> b -> c) -> Prop ((a,b) -> c)
prop_uncurry_f_equal f = prove (uncurry f =:= uncurry' f)

-- Only true for finite tuples, by induction (!)
-- Do we need approximation lemma for functions for the two above?
prop_uncurry_f_tuple_equal :: (a -> b -> c) -> (a,b) -> Prop c
prop_uncurry_f_tuple_equal f t = prove (uncurry f t =:= uncurry' f t)

prop_uncurry_f_unboxedtuple_equal :: (a -> b -> c) -> a -> b -> Prop c
prop_uncurry_f_unboxedtuple_equal f a b = prove (uncurry f (a,b) =:= uncurry' f (a,b))

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

prop_left_idl :: (a -> b) -> Prop (a -> b)
prop_left_idl f = prove (f . id =:= f)

prop_right_idl :: (a -> b) -> Prop (a -> b)
prop_right_idl f = prove (id . f =:= f)

prop_left_id :: (a -> b) -> Prop (a -> b)
prop_left_id f = prove (f ... id =:= f)

prop_right_id :: (a -> b) -> Prop (a -> b)
prop_right_id f = prove (id ... f =:= f)