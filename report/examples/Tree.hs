data Tree a = Empty | Branch (Tree a) a (Tree a)

leaf :: a -> Tree a
leaf x = Branch Empty x Empty

top :: Tree a -> a
top (Branch _ x _) = x

mirror :: Tree a -> Tree a
mirror (Branch l x r) = Branch (mirror l) x (mirror r)
mirror Empty          = Empty

unbalance :: Tree a -> Tree a
unbalance (Branch (Branch l x r) y r') = unbalance (Branch l x (Branch r y r'))
unbalance (Branch l x r)               = Branch l x (unbalance r)
unbalance Empty                        = Empty

