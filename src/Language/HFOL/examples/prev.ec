data T 2;
data Cons 2 Nil 0;
data Succ 1 Zero 0;

taily a b = case T a b of
  { T (Cons x xs) (Cons y ys) -> ys
  ; T (Cons x xs) Nil         -> xs
  ; _                            -> Nil
  };

prev a b = case T a b of
  { T (Cons Zero xs) (Cons (Succ n) ys) -> ys
  ; T (Cons n xs)    _                  -> xs
  ; _                                   -> Nil
  };