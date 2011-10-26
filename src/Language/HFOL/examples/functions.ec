data T 2;
data A 0 B 0 C 0 D 0;
data Cons 2 Nil 0;
data J 1 N 0;

t f p x = case f x of
          { T a b | p a -> A
          ; _           -> C
          };

s p q a = case T (f a) (g a) of
            { T (J x) (J y) | p x -> A
            ; T N     (J y) | q y -> B
            ; T (J x) N     | q x -> C
            ; _                   -> D
            };

f x = x;
g x = x;

