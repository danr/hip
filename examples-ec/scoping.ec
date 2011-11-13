data List a = Cons a (List a) | Nil;
data T a b = T a b;

bugged p a b = case T a b of
            { T x y | p x -> x
            ; x           -> b
            };

fixed p a b = case T a b of
            { T x y | p x -> x
            ; r           -> b
            };

loop xs = case xs of
          { Cons x xs -> xs
          ; Nil       -> Nil
          };

mystery x y p = case T x y of
            { T y x | p y -> y
            ; T x y       -> z
            };