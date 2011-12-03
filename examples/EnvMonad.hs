-- No properties of local yet
module EnvMonad where

import Prelude ()

infix 1 =:=
type Prop a = a
prove = prove
(=:=) = (=:=)

type Env e a = e -> a

(>>=) :: Env e a -> (a -> Env e b) -> Env e b
f >>= g = \e -> g (f e) e

(>>==) :: Env e a -> (a -> Env e b) -> Env e b
(f >>== g) e = g (f e) e

return :: a -> Env e a
return a e = a

returnl :: a -> Env e a
returnl a = \e -> a

-- Bind with lambda --------------------------------------------------------

prop_return_leftl :: (e -> a) -> Prop (e -> a)
prop_return_leftl f = prove ((f >>= return) =:= f)

prop_return_rightl :: (a -> e -> a) -> a -> Prop (e -> a)
prop_return_rightl f a = prove ((return a >>= f) =:= f a)

prop_assocl :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> Prop (e -> c)
prop_assocl m f g = prove (((m >>= f) >>= g) =:= (m >>= (\x -> f x >>= g)))

-- Bind without lambda --------------------------------------------------------

prop_return_left :: (e -> a) -> Prop (e -> a)
prop_return_left f = prove ((f >>== return) =:= f)

prop_return_right :: (a -> e -> a) -> a -> Prop (e -> a)
prop_return_right f a = prove ((return a >>== f) =:= f a)

prop_assoc :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> Prop (e -> c)
prop_assoc m f g = prove (((m >>== f) >>== g) =:= (m >>== (\x -> f x >>== g)))

-- With lambda return ---------------------------------------------------------

prop_returnl_leftl :: (e -> a) -> Prop (e -> a)
prop_returnl_leftl f = prove ((f >>= returnl) =:= f)

prop_returnl_rightl :: (a -> e -> a) -> a -> Prop (e -> a)
prop_returnl_rightl f a = prove ((returnl a >>= f) =:= f a)

prop_returnl_left :: (e -> a) -> Prop (e -> a)
prop_returnl_left f = prove ((f >>== returnl) =:= f)

prop_returnl_right :: (a -> e -> a) -> a -> Prop (e -> a)
prop_returnl_right f a = prove ((returnl a >>== f) =:= f a)

-- Let's join and fmap these beasts -------------------------------------------

id x = x

fmapl f m = m >>= (\x -> return (f x))
joinl n = n >>= id
fmap f m = m >>== (\x -> return (f x))
join n = n >>== id

fmaplrl f m = m >>= (\x -> returnl (f x))
joinlrl n = n >>= id
fmaprl f m = m >>== (\x -> returnl (f x))
joinrl n = n >>== id

prop_fmapl_id :: Prop (a -> (a,s))
prop_fmapl_id = prove (fmapl id =:= id)
prop_fmap_id :: Prop (a -> (a,s))
prop_fmap_id = prove (fmap id =:= id)
prop_fmaplrl_idl :: Prop (a -> (a,s))
prop_fmaplrl_idl = prove (fmaplrl id =:= id)
prop_fmaprl_id :: Prop (a -> (a,s))
prop_fmaprl_id = prove (fmaprl id =:= id)

-- Let's just go with the non-lambda definition
(f . g) x = f (g x)

prop_fmap_comp :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmap_comp f g = prove (fmap (f . g) =:= fmap f . fmap g)
prop_fmaprl_comp :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmaprl_comp f g = prove (fmaprl (f . g) =:= fmaprl f . fmaprl g)
prop_fmapl_comp :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmapl_comp f g = prove (fmapl (f . g) =:= fmapl f . fmapl g)
prop_fmaplrl_comp :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmaplrl_comp f g = prove (fmaplrl (f . g) =:= fmaplrl f . fmaplrl g)
