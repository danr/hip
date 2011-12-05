-- Does not yet check put/get properties!
module StateMonad where

import Prelude ()


type State s a = s -> (a,s)

uncurry f (a,b) = f a b
uncurry' f t = f (fst t) (snd t)


fst (a,b) = a
snd (a,b) = b


bind1 :: State s a -> (a -> State s b) -> State s b
(m `bind1` f) s = uncurry f (m s)

bind2 :: State s a -> (a -> State s b) -> State s b
(m `bind2` f) s = uncurry' f (m s)

bind3 :: State s a -> (a -> State s b) -> State s b
(m `bind3` f) s = let a  = fst (m s)
                      s' = snd (m s)
                  in  f a s'

bind1l :: State s a -> (a -> State s b) -> State s b
m `bind1l` f = \s -> uncurry f (m s)

bind2l :: State s a -> (a -> State s b) -> State s b
m `bind2l` f = \s -> uncurry' f (m s)

bind3l :: State s a -> (a -> State s b) -> State s b
m `bind3l` f = \s -> let a  = fst (m s)
                         s' = snd (m s)
                     in  f a s'


return :: a -> State s a
return x s = (x,s)


returnl :: a -> State s a
returnl x = \s -> (x,s)

-- Bind without lambda --------------------------------------------------------

prop_return_left1 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left1 f = (f `bind1` return) =:= f

prop_return_right1 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right1 f a = (return a `bind1` f) =:= f a

prop_assoc1 :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc1 m f g = ((m `bind1` f) `bind1` g) =:= (m `bind1` (\x -> f x `bind1` g))

prop_return_left2 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left2 f = (f `bind2` return) =:= f

prop_return_right2 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right2 f a = (return a `bind2` f) =:= f a

prop_assoc2 :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc2 m f g = ((m `bind2` f) `bind2` g) =:= (m `bind2` (\x -> f x `bind2` g))

prop_return_left3 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left3 f = (f `bind3` return) =:= f

prop_return_right3 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right3 f a = (return a `bind3` f) =:= f a

prop_assoc3 :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc3 m f g = ((m `bind3` f) `bind3` g) =:= (m `bind3` (\x -> f x `bind3` g))

-- Lambda definition ----------------------------------------------------------

prop_return_left1l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left1l f = (f `bind1l` return) =:= f

prop_return_right1l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right1l f a = (return a `bind1l` f) =:= f a

prop_assoc1l :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc1l m f g = ((m `bind1l` f) `bind1l` g) =:= (m `bind1l` (\x -> f x `bind1l` g))

prop_return_left2l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left2l f = (f `bind2l` return) =:= f

prop_return_right2l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right2l f a = (return a `bind2l` f) =:= f a

prop_assoc2l :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc2l m f g = ((m `bind2l` f) `bind2l` g) =:= (m `bind2l` (\x -> f x `bind2l` g))

prop_return_left3l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left3l f = (f `bind3l` return) =:= f

prop_return_right3l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right3l f a = (return a `bind3l` f) =:= f a

prop_assoc3l :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc3l m f g = ((m `bind3l` f) `bind3l` g) =:= (m `bind3l` (\x -> f x `bind3l` g))

-- And the same with return as lambda -----------------------------------------

prop_returnl_left1 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left1 f = (f `bind1` returnl) =:= f

prop_returnl_right1 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right1 f a = (returnl a `bind1` f) =:= f a

prop_returnl_left2 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left2 f = (f `bind2` returnl) =:= f

prop_returnl_right2 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right2 f a = (returnl a `bind2` f) =:= f a

prop_returnl_left3 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left3 f = (f `bind3` returnl) =:= f

prop_returnl_right3 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right3 f a = (returnl a `bind3` f) =:= f a

prop_returnl_left1l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left1l f = (f `bind1l` returnl) =:= f

prop_returnl_right1l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right1l f a = (returnl a `bind1l` f) =:= f a

prop_returnl_left2l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left2l f = (f `bind2l` returnl) =:= f

prop_returnl_right2l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right2l f a = (returnl a `bind2l` f) =:= f a

prop_returnl_left3l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left3l f = (f `bind3l` returnl) =:= f

prop_returnl_right3l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right3l f a = (returnl a `bind3l` f) =:= f a

-- Let's also try something with kliesli-composition
(>=>) :: (a -> State s b) -> (b -> State s c) -> a -> State s c
m >=> n = \a s -> uncurry n (m a s)

prop_right_kliesli :: (a -> State s b) -> Prop (a -> State s d)
prop_right_kliesli f = (f >=> return) =:= f

prop_left_kliesli :: (a -> State s b) -> Prop (a -> State s d)
prop_left_kliesli f = (return >=> f) =:= f

prop_assoc_kliesli :: (a -> State s b) -> (b -> State s c) -> (c -> State s d) -> Prop (a -> State s d)
prop_assoc_kliesli f g h = ((f >=> g) >=> h) =:= (f >=> (g >=> h))

-- Let's join and fmap these beasts -------------------------------------------

id x = x

fmap1l f m = m `bind1l` (\x -> return (f x))
join1l n = n `bind1l` id
fmap2l f m = m `bind2l` (\x -> return (f x))
join2l n = n `bind2l` id
fmap3l f m = m `bind3l` (\x -> return (f x))
join3l n = n `bind3l` id
fmap1 f m = m `bind1` (\x -> return (f x))
join1 n = n `bind1` id
fmap2 f m = m `bind2` (\x -> return (f x))
join2 n = n `bind2` id
fmap3 f m = m `bind3` (\x -> return (f x))
join3 n = n `bind3` id

prop_fmap_id1l :: Prop (a -> (a,s))
prop_fmap_id1l = fmap1l id =:= id
prop_fmap_id2l :: Prop (a -> (a,s))
prop_fmap_id2l = fmap2l id =:= id
prop_fmap_id3l :: Prop (a -> (a,s))
prop_fmap_id3l = fmap3l id =:= id
prop_fmap_id1 :: Prop (a -> (a,s))
prop_fmap_id1 = fmap1 id =:= id
prop_fmap_id2 :: Prop (a -> (a,s))
prop_fmap_id2 = fmap2 id =:= id
prop_fmap_id3 :: Prop (a -> (a,s))
prop_fmap_id3 = fmap3 id =:= id

-- Let's just go with the non-lambda definition
(f . g) x = f (g x)

prop_fmap_comp1l :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmap_comp1l f g = fmap1l (f . g) =:= fmap1l f . fmap1l g
prop_fmap_comp2l :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmap_comp2l f g = fmap2l (f . g) =:= fmap2l f . fmap2l g
prop_fmap_comp3l :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmap_comp3l f g = fmap3l (f . g) =:= fmap3l f . fmap3l g
prop_fmap_comp1 :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmap_comp1 f g = fmap1 (f . g) =:= fmap1 f . fmap1 g
prop_fmap_comp2 :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmap_comp2 f g = fmap2 (f . g) =:= fmap2 f . fmap2 g
prop_fmap_comp3 :: (b -> c) -> (a -> b) -> Prop (a -> (c,s))
prop_fmap_comp3 f g = fmap3 (f . g) =:= fmap3 f . fmap3 g



{- more properties for later :)

return . f = fmap f . return

join . fmap join = join . join
join . fmap return = join . return = id
join . fmap (fmap f) = fmap f . join
-}

