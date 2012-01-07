module BoolExpr where

import Prelude (Bool(..))

data Expr = Expr :&: Expr | Value Bool

True  && x = x
False && _ = False

eval :: Expr -> Bool
eval (e1 :&: e2) = eval e1 && eval e2
eval (Value b)   = b

mirror :: Expr -> Expr
mirror (e1 :&: e2) = mirror e2 :&: mirror e1
mirror (Value b)   = Value b

prop_mirror_eval :: Expr -> Prop Bool
prop_mirror_eval e = eval (mirror e) =:= eval e

prop_mirror_mirror :: Expr -> Prop Expr
prop_mirror_mirror e = mirror (mirror e) =:= e