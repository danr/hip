module Functions where

infix 1 =:=
type Prop a = a
prove :: a -> Prop a
prove = prove
proveBool :: a -> Prop Bool
proveBool = proveBool
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
prop_dans_nonidentity x y = prove (const x =:= id x)