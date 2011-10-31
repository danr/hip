import Test.QuickCheck
import Control.Applicative

data Expr = Add Expr Expr
          | Mul Expr Expr
          | IsZero Expr
          | Val Nat
  deriving (Eq,Show)

instance Arbitrary Expr where
  arbitrary = sized arbExpr
    where
      arbExpr s = frequency [(s ,IsZero <$> arbExpr (s-1))
                            ,(s',Add    <$> arbExpr s' <*> arbExpr s')
                            ,(s',Mul    <$> arbExpr s' <*> arbExpr s')
                            ,(1 ,Val    <$> arbitrary)
                           ]
        where s' = s `div `2

data Nat = S Nat | Z deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in sized $ \s -> do
          x <- choose (0,s)
          return (nats !! x)

mirror :: Expr -> Expr
mirror (Add e1 e2) = Add (mirror e2) (mirror e1)
mirror (Mul e1 e2) = Mul (mirror e2) (mirror e1)
mirror (IsZero e)  = IsZero (mirror e)
mirror e           = e

prop_mirror :: Expr -> Bool
prop_mirror e = e == mirror (mirror e)

plus x Z     = x
plus x (S y) = S (plus x y)

size :: Expr -> Nat
size (Add e1 e2) = size e1 `plus` size e2
size (Mul e1 e2) = size e1 `plus` size e2
size (IsZero e)  = size e
size (Val _)     = S Z

prop_mirror_size :: Expr -> Bool
prop_mirror_size e = size e == size (mirror e)

times x Z     = Z
times x (S y) = (x `times` y) `plus` x

eval :: Expr -> Nat
eval (Add e1 e2) = eval e1 `plus` eval e2
eval (Mul e1 e2) = eval e1 `times` eval e2
eval (IsZero e)  | eval e == Z = S Z
                 | otherwise   = Z
eval (Val n) = n

prop_mirror_eval :: Expr -> Bool
prop_mirror_eval e = eval e == eval (mirror e)