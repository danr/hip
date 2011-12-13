-- Uses nat as variables (but not as de bruijn indicies)

import Control.Applicative
import Test.QuickCheck

data Nat = S Nat | Z deriving (Eq,Show)

data Lam = Var Nat | Lam :@ Lam | Abs Nat Lam deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in sized $ \s -> do
          x <- choose (0,s)
          return (nats !! x)

instance Arbitrary Lam where
  arbitrary = sized arbLam
    where
      arbLam s = frequency [(s ,Abs  <$> arbitrary <*> arbLam (s-1))
                           ,(s',(:@) <$> arbLam s' <*> arbLam s')
                           ,(1 ,Var  <$> arbitrary)
                           ]
        where s' = s `div `2

mem :: Nat -> [Nat] -> Bool
u `mem` (x:xs) = (u == x) `boolOr` (u `mem` xs)
u `mem` []     = False

boolOr True  x = True
boolOr False x = x

boolNot True = False
boolNot False = True

boolAnd True  x = x
boolAnd False x = False

boolEq True True = True
boolEq False False = True
boolEq x y = False

union :: [Nat] -> [Nat] -> [Nat]
union (x:xs) ys | x `mem` ys = union xs ys
                | otherwise  = x:union xs ys
union []     ys              = ys

delete' u (x:xs) | x == u    = delete' u xs
                 | otherwise = x : delete' u xs
delete' u []                 = []

freeVars :: Lam -> [Nat]
freeVars (Var x)    = [x]
freeVars (e1 :@ e2) = freeVars e1 `union` freeVars e2
freeVars (Abs x e)  = delete' x (freeVars e)

freeIn :: Nat -> Lam -> Bool
v `freeIn` e = go e []
  where
    go :: Lam -> [Nat] -> Bool
    go (Var x)    env = (v == x) `boolAnd` boolNot (v `mem` env)
    go (e1 :@ e2) env = go e1 env `boolOr` go e2 env
    go (Abs x e)  env = go e (x:env)

prop_free :: Lam -> Nat -> Bool
prop_free e v = (v `mem` freeVars e) == (v `freeIn` e)

