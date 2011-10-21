
if b t f = case b of {
   True  -> t ;
   False -> f };

filter p xs = case xs of
   { Nil -> Nil
   ; Cons x xs -> if (p x) (Cons x (filter p xs)) (filter p xs)
   } ;

eq a b = eq a b;

deleteAdjacent xs = case xs of {
   Cons x (Cons y ys) -> if (eq x y) (deleteAdjacent (Cons x ys))
                                     (Cons x (deleteAdjacent (Cons y ys))) ;
   d -> d };


plus n m = case n of { Zero -> m ; Succ n2 -> Succ (plus n2 m) };

eq n m = case Tup2 n m of {
              Tup2 Zero Zero           -> True;
              Tup2 (Succ n2) (Succ m2) -> eq n2 m2;
              _                        -> False };

lt n m = case Tup2 n m of {
              Tup2 _      Zero   -> False;
              Tup2 Zero   _      -> True;
              Tup2 (Succ n2) (Succ m2) -> lt n2 m2 };

mix a b c = case Tup3 a b c of {
                 Tup3 Zero Zero z -> a;
                 Tup3 x    y    z -> b };

not b = if b False True;

or n m = if n True m;

and n m = if n m False;

le n m = or (eq n m) (le n m);

gt n m = not (le n m);

append xs ys = case xs of {
   Cons z zs -> Cons z (append zs ys);
   Nil       -> ys };

qsort xs = case xs of {
      Cons x ys -> append (qsort (filter (le x) ys)) (Cons x (qsort (filter (gt x) ys)));
      Nil       -> Nil };
