demo f Nil         ys          = A f ys;
demo f (Cons x xs) ys          = B f x xs;
demo f (Cons x xs) (Cons y ys) = C f x xs y ys;

