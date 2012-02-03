module BoolExpr where

import AutoPrelude
import Prelude(Bool(..))

False || b = b
True  || b = True

True  && b = True
False && b = b

True !&& True = False
_    !&& _    = True

data Expr = And  Expr Expr
          | Or   Expr Expr
          | Value Bool

data NExpr = NAnd NExpr NExpr
           | NValue Bool

notExpr :: NExpr -> NExpr
notExpr e1 = NAnd e1 e1

toNExpr :: Expr -> NExpr
toNExpr (And e1 e2) = notExpr (NAnd (toNExpr e1) (toNExpr e2))
toNExpr (Or e1 e2)  = (NAnd (notExpr (toNExpr e1)) (notExpr (toNExpr e2)))
toNExpr (Value b)   = NValue b

eval :: Expr -> Bool
eval (And e1 e2) = eval e1 && eval e2
eval (Or e1 e2)  = eval e1 || eval e2
eval (Value b)   = b

evalN :: NExpr -> Bool
evalN (NAnd e1 e2) = evalN e1 !&& evalN e2
evalN (NValue b)   = b

prop_toNExpr :: Expr -> Prop Bool
prop_toNExpr e = eval e =:= evalN (toNExpr e)

