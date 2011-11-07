data T 2;
data Cons 2 Nil 0;
data Zero 0 Succ 1;
data U 0;

if b t f = case b of {
   True  -> t ;
   False -> f };

filter p xs = case xs of
    { Cons x xs | p x -> Cons x (filter p xs)
    ; Cons x xs       -> filter p xs
    ; Nil             -> Nil
    };

plus n m = case n of { Zero -> m ; Succ n -> Succ (plus n m) };

eq n m = case T n m of {
              T Zero Zero         -> True;
              T (Succ n) (Succ m) -> eq n m;
              _                   -> False };

lt n m = case T n m of {
              T _        Zero     -> False;
              T Zero     _        -> True;
              T (Succ n) (Succ m) -> lt n m };

le n m = case U of
           { U | eq n m -> True
           ; U | lt n m -> True
           ; U          -> False
           } ;

gt n m = case U of
           { _ | le n m -> False
           ; _          -> True
           };

append xs ys = case xs of {
   Cons x xs -> Cons x (append xs ys);
   Nil       -> ys };

qsort xs = case xs of
      { Cons x xs -> append (qsort (filter (gt x) xs))
                            (Cons x (qsort (filter (le x) xs)))
      ; Nil       -> Nil
      };

