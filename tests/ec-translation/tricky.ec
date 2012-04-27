data L a = C a (L a) | N;

anyAndFirst p q xs = case filter p xs of
    { C x _ | q x -> True
    ; _           -> False
    };

filter p xs = case xs of
    { C y ys | p y -> C y (filter p ys)
    ; C y ys       -> filter p ys
    ; N            -> N
    };
