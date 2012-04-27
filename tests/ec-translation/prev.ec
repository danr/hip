data List a = Cons a (List a) | Nil;
data Nat = Succ Nat | Zero;
data T a b = T a b;

taily a b = case T a b of
  { T (Cons x xs) (Cons y ys) -> ys
  ; T (Cons x xs) Nil         -> xs
  ; _                            -> Nil
  };

prev a b = case T a b of
  { T (Cons Zero xs) (Cons (Succ n) ys) -> ys
  ; T (Cons n zs)    _                  -> zs
  ; _                                   -> Nil
  };

skippy a b = case T a b of
  { T Nil (Cons (Succ n) ys) -> ys
  ; T Nil zs                 -> zs
  ; _                      -> Nil
  };

skipZero xs = case xs of
  { Cons (Succ n) ys -> ys
  ; _                -> xs
  };