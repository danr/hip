
data Expr = Add Expr Expr
          | Mul Expr Expr
          | IsZero Expr
          | Val Nat
            
mirror :: Expr -> Expr            
mirror (Add e1 e2) = Add (mirror e2) (mirror e1)
mirror (Mul e1 e2) = Mul (mirror e2) (mirror e1)
mirror (IsZero e)  = IsZero (mirror e)
mirror e           = e
