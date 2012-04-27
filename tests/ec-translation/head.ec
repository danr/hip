data List a = Cons a (List a) | Nil;
data T2 a b = T2 a b;

hh (Cons _ (Cons x _)) = x;

hh2 (Cons _ (Cons x _)) (Cons _ (Cons y _)) = T2 x y;
