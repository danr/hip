data C 2 N 0;

anyAndFirst p q xs = case filter p xs of
    { C x _ | q x -> True
    ; _           -> False
    };

filter p xs = case xs of
    { C y ys | p y -> C y (filter p ys)
    ; C y ys       -> filter p ys
    ; N            -> N
    };
