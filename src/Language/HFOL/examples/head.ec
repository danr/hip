data Cons 2 Nil 0;
data Tup1 1;
data Tup2 2;

hh (Cons _ (Cons x _)) = x;

hh2 (Cons _ (Cons x _)) (Cons _ (Cons y _)) = Tup2 x y;
