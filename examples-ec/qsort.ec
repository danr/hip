data List a = Cons a (List a) | Nil;
data Nat = Succ Nat | Zero;
data T a b = T a b;

filter p xs = case xs of
    { Cons y ys | p y -> Cons y (filter p ys)
    ; Cons y ys       -> filter p ys
    ; Nil             -> Nil
    };

plus n m = case n of { Zero -> m ; Succ n2 -> Succ (plus n2 m) };

le n m = case T n m of
            { T Zero      _         -> True
            ; T _         Zero      -> False
            ; T (Succ n2) (Succ m2) -> le n2 m2
            };

gt n m = case T n m of
            { T _         Zero      -> True
            ; T Zero      _         -> False
            ; T (Succ n2) (Succ m2) -> gt n2 m2
            };

append xs ys = case xs of
   { Cons z zs -> Cons z (append zs ys)
   ; Nil       -> ys
   };

qsort xs = case xs of
      { Cons x ys -> append (qsort (filter (gt x) ys))
                            (Cons x (qsort (filter (le x) ys)))
      ; Nil       -> Nil
      };

zero = Zero;
one  = Succ zero;
two  = Succ two;

list = Cons one (Cons zero Nil);
