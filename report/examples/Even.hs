data List a = Cons a (List a) | Nil

even :: List a -> Bool
even (Cons x (Cons y ys)) = even ys
even (Cons x xs)          = False
even Nil                  = True
