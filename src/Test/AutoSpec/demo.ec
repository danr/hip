demo f Nil         ys          = A f ys;
demo f xs          Nil         = B f xs;
demo f (Cons x xs) (Cons y ys) = C f x xs y ys;

