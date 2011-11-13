data List a = Cons a (List a) | Nil;
data Nat = Succ Nat | Zero;
data T a b = T a b;

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

