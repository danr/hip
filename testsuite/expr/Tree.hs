module Tree where

import Prelude ()

infix 1 :=:

data Equals a = (:=:) a a

data Prop a
  = Prove (Equals a)

prove :: Equals -> Prop
prove x = Prove x

data T a = L | N a | B (T a) a (T a)

mirror :: Tree a -> Tree a
mirror L = L
mirror (N x) = N x
mirror (B l x r) = B (mirror l) x (mirror r)


prop_mirror_idem :: T a -> Prop (T a)
prop_mirror_idem t = prove (mirror (mirror t) :=: t)
