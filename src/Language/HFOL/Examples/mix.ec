
data T 2;
data T3 3;
data Cons 2 Nil 0;
data Zero 0 Succ 1;

mix a b = case T a b of
               { T Zero y -> a
               ; T x    y -> b
               };

const a b = a;

mix2 a b = case const a b of
               { Zero -> a
               ; x    -> b
               };

mix3 a b = case T3 a    b (const a b) of
             { T3 Zero y    z -> z
             ; T3 x    Zero z -> const x z
             ; _              -> b
             };

