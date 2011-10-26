data True 0 False 0;
data Cons 2 Nil 0;

filterOr p q xs = case xs of
    { Cons y ys | p y -> Cons y (filterOr p q ys)
    ; Cons y ys | q y -> Cons y (filterOr p q ys)
    ; Cons y ys       -> filterOr p q ys
    ; Nil             -> Nil
    };

