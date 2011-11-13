data List a = Cons a (List a) | Nil;

hh (Cons _ (Cons x _)) = x;

hh2 (Cons _ (Cons x _)) (Cons _ (Cons y _)) = T2 x y;
