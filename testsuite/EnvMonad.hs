-- No properties of local yet
module EnvMonad where

import AutoPrelude
import Prelude ()

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
prop_return_leftl f = (f >>= return) =:= f

prop_return_rightl :: (a -> e -> a) -> a -> Prop (e -> a)
prop_return_rightl f a = (return a >>= f) =:= f a

prop_assocl :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> Prop (e -> c)
prop_assocl m f g = ((m >>= f) >>= g) =:= (m >>= (\x -> f x >>= g))

-- Bind without lambda --------------------------------------------------------

prop_return_left :: (e -> a) -> Prop (e -> a)
prop_return_left f = (f >>== return) =:= f

prop_return_right :: (a -> e -> a) -> a -> Prop (e -> a)
prop_return_right f a = (return a >>== f) =:= f a

prop_assoc :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> Prop (e -> c)
prop_assoc m f g = ((m >>== f) >>== g) =:= (m >>== (\x -> f x >>== g))

-- With lambda return ---------------------------------------------------------

prop_returnl_leftl :: (e -> a) -> Prop (e -> a)
prop_returnl_leftl f = (f >>= returnl) =:= f

prop_returnl_rightl :: (a -> e -> a) -> a -> Prop (e -> a)
prop_returnl_rightl f a = (returnl a >>= f) =:= f a

prop_returnl_left :: (e -> a) -> Prop (e -> a)
prop_returnl_left f = (f >>== returnl) =:= f

prop_returnl_right :: (a -> e -> a) -> a -> Prop (e -> a)
prop_returnl_right f a = (returnl a >>== f) =:= f a

-- With applied environment ---------------------------------------------------

{-
prop_app_return_leftl :: (e -> a) -> e -> Prop a
prop_app_return_leftl f e = (f >>= return) e =:= f e

prop_app_return_rightl :: (a -> e -> a) -> a -> e -> Prop a
prop_app_return_rightl f a e = (return a >>= f) e =:= f a e

prop_app_assocl :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> e -> Prop c
prop_app_assocl m f g e = ((m >>= f) >>= g) e =:= (m >>= (\x -> f x >>= g)) e

prop_app_return_left :: (e -> a) -> e -> Prop a
prop_app_return_left f e = (f >>== return) e =:= f e

prop_app_return_right :: (a -> e -> a) -> a -> e -> Prop a
prop_app_return_right f a e = (return a >>== f) e =:= f a e

prop_app_assoc :: (e -> a) -> (a -> e -> b) -> (b -> e -> c) -> e -> Prop c
prop_app_assoc m f g e = ((m >>== f) >>== g) e =:= (m >>== (\x -> f x >>== g)) e


prop_app_returnl_leftl :: (e -> a) -> e -> Prop a
prop_app_returnl_leftl f e = (f >>= returnl) e =:= f e

prop_app_returnl_rightl :: (a -> e -> a) -> a -> e -> Prop a
prop_app_returnl_rightl f a e = (returnl a >>= f) e =:= f a e


prop_app_returnl_left :: (e -> a) -> e -> Prop a
prop_app_returnl_left f e = (f >>== returnl) e =:= f e


prop_app_returnl_right :: (a -> e -> a) -> a -> e -> Prop a
prop_app_returnl_right f a e = (returnl a >>== f) e =:= f a e
-}

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

prop_fmapl_id :: Prop ((e -> a) -> e -> a)
prop_fmapl_id = fmapl id =:= id
prop_fmap_id :: Prop ((e -> a) -> e -> a)
prop_fmap_id = fmap id =:= id
prop_fmaplrl_idl :: Prop ((e -> a) -> e -> a)
prop_fmaplrl_idl = fmaplrl id =:= id
prop_fmaprl_id :: Prop ((e -> a) -> e -> a)
prop_fmaprl_id = fmaprl id =:= id

-- Let's just go with the non-lambda definition
(f . g) x = f (g x)

prop_fmap_comp :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> b)
prop_fmap_comp f g = fmap (f . g) =:= fmap f . fmap g
prop_fmaprl_comp :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> b)
prop_fmaprl_comp f g = fmaprl (f . g) =:= fmaprl f . fmaprl g
prop_fmapl_comp :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> b)
prop_fmapl_comp f g = fmapl (f . g) =:= fmapl f . fmapl g
prop_fmaplrl_comp :: (b -> c) -> (a -> b) -> Prop ((e -> a) -> e -> b)
prop_fmaplrl_comp f g = fmaplrl (f . g) =:= fmaplrl f . fmaplrl g
