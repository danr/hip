
data True 0 False 0;
data T 2;
data Cons 2 Nil 0;
data Zero 0 Succ 1;

if b t f = case b of {
   True  -> t ;
   False -> f };

filter p xs = case xs of
   { Nil -> Nil
   ; Cons x ys -> if (p x) (Cons x (filter p ys)) (filter p ys)
   } ;

plus n m = case n of { Zero -> m ; Succ n2 -> Succ (plus n2 m) };

eq n m = case T n m of {
              T Zero Zero           -> True;
              T (Succ n2) (Succ m2) -> eq n2 m2;
              _                        -> False };

lt n m = case T n m of {
              T _      Zero   -> False;
              T Zero   _      -> True;
              T (Succ n2) (Succ m2) -> lt n2 m2 };

not b = if b False True;

or n m = if n True m;

and n m = if n m False;

le n m = or (eq n m) (le n m);

gt n m = not (le n m);

append xs ys = case xs of {
   Cons z zs -> Cons z (append zs ys);
   Nil       -> ys };

qsort xs = case xs of
      { Cons x ys -> append (qsort (filter (le x) ys))
                            (Cons x (qsort (filter (gt x) ys)))
      ; Nil       -> Nil
      };
