module Tree where

import Prelude ()

infix 1 :=:

data Equals a = (:=:) a a

data Prop a
  = Prove (Equals a)

prove :: Equals -> Prop
prove x = Prove x

data Tree a = Leaf | Node a | Branch (Tree a) a (Tree a)

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node x) = Node x
mirror (Branch l x r) = Branch (mirror l) x (mirror r)

prop_mirror_idem :: Tree a -> Prop (Tree a)
prop_mirror_idem t = prove (mirror (mirror t) :=: t)