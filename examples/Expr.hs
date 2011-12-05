module Expr where

data Expr = Add Expr Expr
          | Mul Expr Expr
          | IsZero Expr
          | Val Nat
  deriving (Eq,Show)

data Nat = Z | S Nat deriving (Eq,Show)

mirror :: Expr -> Expr
mirror (Add e1 e2) = Add (mirror e2) (mirror e1)
mirror (Mul e1 e2) = Mul (mirror e2) (mirror e1)
mirror (IsZero e)  = IsZero (mirror e)
mirror e           = e

prop_mirror :: Expr -> Prop Expr
prop_mirror e = e =:= mirror (mirror e)

plus x Z     = x
plus x (S y) = S (plus x y)

size :: Expr -> Nat
size (Add e1 e2) = size e1 `plus` size e2
size (Mul e1 e2) = size e1 `plus` size e2
size (IsZero e)  = size e
size (Val _)     = S Z

times x Z     = Z
times x (S y) = (x `times` y) `plus` x

eval :: Expr -> Nat
eval (Add e1 e2) = eval e1 `plus` eval e2
eval (Mul e1 e2) = eval e1 `times` eval e2
eval (IsZero e) = case eval e of
                    Z -> S Z
                    _ -> Z
eval (Val n) = n

-- These probably need assoc and identity lemmas
prop_mirror_size :: Expr -> Prop Nat
prop_mirror_size e = size e =:= size (mirror e)

prop_mirror_eval :: Expr -> Prop Expr
prop_mirror_eval e = eval e =:= eval (mirror e)
