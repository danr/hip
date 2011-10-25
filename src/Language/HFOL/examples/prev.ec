taily a b = case Tup2 a b of
  { Tup2 (Cons x xs) (Cons y ys) -> ys
  ; Tup2 (Cons x xs) Nil         -> xs
  ; _                            -> Nil
  };

prev a b = case Tup2 a b of
  { Tup2 (Cons Zero xs) (Cons (Succ n) ys) -> ys
  ; Tup2 (Cons n xs)    _                  -> xs
  ; _                                      -> Nil
  };