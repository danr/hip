
data T 2;
data T3 3;
data Cons 2 Nil 0;
data Zero 0 Succ 1;
data True 0 False 0;

mix p a b = case T a b of
               { T Zero y | p y -> a
               ; T x    y -> b
               };

const a b = a;

mix2 p a b = case const a b of
               { Zero -> a
               ; x    | p x -> b
               };

mix3 p q a b = case T3 a    b (const a b) of
             { T3 x    Zero z | q x -> const x z
             ; _              | p a -> b
             ; r                    -> a
             };

