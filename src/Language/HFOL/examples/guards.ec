data True 0 False 0;
data Cons 2 Nil 0;

if b t f = case b of
    { True  -> t
    ; False -> f
    };

if2 b t f = case b of
    { True -> t
    ; _    -> f
    };

filter p xs = case xs of
    { Cons y ys | p y -> Cons y (filter p ys)
    ; Cons y ys       -> filter p ys
    ; _               -> Nil
    };

filter2 p xs = case xs of
    { Cons y ys | p y -> Cons y (filter2 p ys)
    ; Cons y ys       -> filter2 p ys
    ; Nil             -> Nil
    };

not b = case b of { True -> False ; False -> True };

filter3 p xs = case xs of
    { Cons y ys | p y       -> Cons y (filter3 p ys)
    ; Cons y ys | not (p y) -> filter3 p ys
    ; Nil                   -> Nil
    };

anyAndFirst p q xs = case filter p xs of
    { Cons x _ | q x -> True
    ; _              -> False
    };