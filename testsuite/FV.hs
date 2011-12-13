module FV where

import AutoPrelude

(=:=) :: a -> a -> a
(=:=) = (=:=)

data Nat = S Nat | Z

data Lam = Var Nat | Lam :@ Lam | Abs Nat Lam

otherwise = True

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

mem :: Nat -> [Nat] -> Bool
mem x (y:ys) | x == y    = True
             | otherwise = x `mem` ys
mem x [] = False

union (x:xs) ys | x `mem` ys = union xs ys
                | otherwise  = x:union xs ys
union []     ys              = ys

delete u (x:xs) | x == u    = delete u xs
                | otherwise = x : delete u xs
delete u []                 = []

freeVars :: Lam -> [Nat]
freeVars (Var x)    = [x]
freeVars (e1 :@ e2) = freeVars e1 `union` freeVars e2
freeVars (Abs x e)  = delete x (freeVars e)

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

prop_free :: Lam -> Nat -> Prop Bool
prop_free e v = v `mem` freeVars e =:= v `freeIn` e
