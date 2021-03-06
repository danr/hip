data T a b = T a b;
data W = A | B | C;
data List a = Cons a (List a) | Nil;

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

t f x p q = case f x of
           { Cons y ys | p y -> A
           ; Cons y ys | q y -> B
           ; _               -> C
           };

s f g p q r x z w = case T (f x) (g x) of
            { T (Cons y ys) (Cons z zs) | p y -> y
            ; T Nil         (Cons z zs) | q z -> z
            ; T (Cons y ys) Nil         | r y -> x
            ; _                               -> w
            };
