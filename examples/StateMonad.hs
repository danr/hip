-- Does not yet check put/get properties!
module StateMonad where

import Prelude ()

infix 1 =:=
type Prop a = a
prove = prove
(=:=) = (=:=)


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
prop_return_left1 f = prove ((f `bind1` return) =:= f)

prop_return_right1 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right1 f a = prove ((return a `bind1` f) =:= f a)

prop_assoc1 :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc1 m f g = prove (((m `bind1` f) `bind1` g) =:= (m `bind1` (\x -> f x `bind1` g)))

prop_return_left2 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left2 f = prove ((f `bind2` return) =:= f)

prop_return_right2 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right2 f a = prove ((return a `bind2` f) =:= f a)

prop_assoc2 :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc2 m f g = prove (((m `bind2` f) `bind2` g) =:= (m `bind2` (\x -> f x `bind2` g)))

prop_return_left3 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left3 f = prove ((f `bind3` return) =:= f)

prop_return_right3 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right3 f a = prove ((return a `bind3` f) =:= f a)

prop_assoc3 :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc3 m f g = prove (((m `bind3` f) `bind3` g) =:= (m `bind3` (\x -> f x `bind3` g)))

-- Lambda definition ----------------------------------------------------------

prop_return_left1l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left1l f = prove ((f `bind1l` return) =:= f)

prop_return_right1l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right1l f a = prove ((return a `bind1l` f) =:= f a)

prop_assoc1l :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc1l m f g = prove (((m `bind1l` f) `bind1l` g) =:= (m `bind1l` (\x -> f x `bind1l` g)))

prop_return_left2l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left2l f = prove ((f `bind2l` return) =:= f)

prop_return_right2l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right2l f a = prove ((return a `bind2l` f) =:= f a)

prop_assoc2l :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc2l m f g = prove (((m `bind2l` f) `bind2l` g) =:= (m `bind2l` (\x -> f x `bind2l` g)))

prop_return_left3l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_return_left3l f = prove ((f `bind3l` return) =:= f)

prop_return_right3l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_return_right3l f a = prove ((return a `bind3l` f) =:= f a)

prop_assoc3l :: (s -> (a,s)) -> (a -> s -> (b,s)) -> (b -> s -> (c,s)) -> Prop (s -> (c,s))
prop_assoc3l m f g = prove (((m `bind3l` f) `bind3l` g) =:= (m `bind3l` (\x -> f x `bind3l` g)))

-- And the same with return as lambda -----------------------------------------

prop_returnl_left1 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left1 f = prove ((f `bind1` returnl) =:= f)

prop_returnl_right1 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right1 f a = prove ((returnl a `bind1` f) =:= f a)

prop_returnl_left2 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left2 f = prove ((f `bind2` returnl) =:= f)

prop_returnl_right2 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right2 f a = prove ((returnl a `bind2` f) =:= f a)

prop_returnl_left3 :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left3 f = prove ((f `bind3` returnl) =:= f)

prop_returnl_right3 :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right3 f a = prove ((returnl a `bind3` f) =:= f a)

prop_returnl_left1l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left1l f = prove ((f `bind1l` returnl) =:= f)

prop_returnl_right1l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right1l f a = prove ((returnl a `bind1l` f) =:= f a)

prop_returnl_left2l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left2l f = prove ((f `bind2l` returnl) =:= f)

prop_returnl_right2l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right2l f a = prove ((returnl a `bind2l` f) =:= f a)

prop_returnl_left3l :: (s -> (a,s)) -> Prop (s -> (a,s))
prop_returnl_left3l f = prove ((f `bind3l` returnl) =:= f)

prop_returnl_right3l :: (a -> s -> (a,s)) -> a -> Prop (s -> (a,s))
prop_returnl_right3l f a = prove ((returnl a `bind3l` f) =:= f a)

-- Let's also try something with kliesli-composition
(>=>) :: (a -> State s b) -> (b -> State s c) -> a -> State s c
m >=> n = \a s -> uncurry n (m a s)

prop_right_kliesli :: (a -> State s b) -> Prop (a -> State s d)
prop_right_kliesli f = prove ((f >=> return) =:= f)

prop_left_kliesli :: (a -> State s b) -> Prop (a -> State s d)
prop_left_kliesli f = prove ((return >=> f) =:= f)

prop_assoc_kliesli :: (a -> State s b) -> (b -> State s c) -> (c -> State s d) -> Prop (a -> State s d)
prop_assoc_kliesli f g h = prove (((f >=> g) >=> h) =:= (f >=> (g >=> h)))

