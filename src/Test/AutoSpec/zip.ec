zip Nil ys = Nil;
zip (Cons x xs) Nil = Nil;
zip (Cons x xs) (Cons y ys) = Cons (Pair x y) (zip xs ys);