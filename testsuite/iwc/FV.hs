-- Uses nat as variables (but not as de bruijn indicies)

import Control.Applicative

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
      arbLam s = [(s - 1,Abs <$> arbitrary <*> arbLam (s-1))
                 ,(s'   ,App <$> arbLam s' <*> arbLam s')
                 ,(1    ,Var <$> arbitrary)
                 ]
        where s' = s `div `2

union (x:xs) ys | x `mem` ys = union xs ys
                | otherwise  = x:union xs ys
union []     ys              = ys

delete' u (x:xs) | x == u    = delete u xs
                 | otherwise = x : delete u xs
delete' u []                 = []

freeVars :: Lam -> [Nat]
freeVars (Var x)    = [x]
freeVars (e1 :@ e2) = freeVars e1 `union` freeVars e2
freeVars (Abs x e)  = delete' x (freeVars e)

boolOr True  x = True
boolOr False x = x

boolNot True = False
boolNot False = False

boolAnd True  x = x
boolAnd False x = False

boolEq True True = True
boolEq False False = True
boolEq x y = False

freeIn :: Var -> Lam -> Bool
v `freeIn` e = go e []
  where
    go :: Lam -> [Nat] -> Bool
    go (Var x)    env = v == x `boolAnd` boolNot (v `mem` env)
    go (e1 :@ e2) env = go e1 env `boolOr` go e2 env
    go (Abs x e)  env = go e (x:env)

prop_free :: Lam -> Var -> Bool
prop_free e v = (v `mem` freeVars e) `boolEq` (v `freeIn` e)
