data T a b = T a b;
data W = A | B | C | D;
data List a = Cons a (List a) | Nil;
data M a = J a | N;

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

