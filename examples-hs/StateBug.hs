
type State s a = s -> (a,s)

fst (a,b) = a
snd (a,b) = b

(>>=) :: State s a -> (a -> State s b) -> State s b
m >>= f = \s -> let a  = fst (m s)
                    s' = snd (m s)
                in  f a s'


bind3 :: State s a -> (a -> State s b) -> State s b
(m `bind3` f) s = let a  = fst (m s)
                      s' = snd (m s)
                  in  f a s'

tup x y = (x,y)

test x = tup x

k x = \y -> let z = x in z