data List a = Cons a (List a) | Nil;
data Nat = Succ Nat | Zero;
data T a b = T a b;

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

