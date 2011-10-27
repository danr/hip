data Cons 2 Nil 0;
data Succ 1 Zero 0;
data T 2;

map f xs = case xs of
         { Cons x xs -> Cons (f x) (map f xs)
         ; Nil       -> Nil
         };

approx n xs = case T n xs of
            { T (Succ n) Nil -> Nil
            ; T (Succ n) (Cons x xs) -> Cons x (approx n xs)
            };

iterate f x = Cons x (iterate f (f x));

bimap  f g xs = map f (map g xs);
bimap2 f g xs = map (dot f g) xs;

dot f g x = f (g x);

compose f g = dot f g;