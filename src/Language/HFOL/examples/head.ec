hh xs = case xs of { Cons _ (Cons x _) -> x };

hh2 (Cons _ (Cons x _)) (Cons _ (Cons y _)) = Tup2 x y;