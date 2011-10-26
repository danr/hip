data T 2;
data Cons 2 Nil 0;
data Zero 0 Succ 1;
data U 0;

if b t f = case b of {
   True  -> t ;
   False -> f };

filter p xs = case xs of
    { Cons y ys | p y -> Cons y (filter p ys)
    ; Cons y ys       -> filter p ys
    ; Nil             -> Nil
    };

plus n m = case n of { Zero -> m ; Succ n2 -> Succ (plus n2 m) };

eq n m = case T n m of {
              T Zero Zero           -> True;
              T (Succ n2) (Succ m2) -> eq n2 m2;
              _                     -> False };

lt n m = case T n m of {
              T _      Zero   -> False;
              T Zero   _      -> True;
              T (Succ n2) (Succ m2) -> lt n2 m2 };

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
   Cons z zs -> Cons z (append zs ys);
   Nil       -> ys };

qsort xs = case xs of
      { Cons x ys -> append (qsort (filter (le x) ys))
                            (Cons x (qsort (filter (gt x) ys)))
      ; Nil       -> Nil
      };

