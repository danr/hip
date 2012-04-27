module BoolExpr2 where

import AutoPrelude
import Prelude(Bool(..))

False || b = b
True  || b = True

True  && b = True
False && b = b

True !&& True = False
_    !&& _    = True

True --> False = False
_    --> _     = True

not True  = False
not False = True

data ExprI = Implies ExprI ExprI
           | ValueI Bool

data ExprO = Or  ExprO ExprO
           | Not ExprO
           | ValueO Bool


translate :: ExprI -> ExprO
translate (Implies e1 e2) = Or (Not (translate e1)) (translate e2)
translate (ValueI b)      = ValueO b

evalI :: ExprI -> Bool
evalI (Implies e1 e2) = evalI e1 --> evalI e2
evalI (ValueI b)      = b

evalO :: ExprO -> Bool
evalO (Or e1 e2) = evalO e1 || evalO e2
evalO (Not e)    = not (evalO e)
evalO (ValueO b) = b

prop_translate :: ExprI -> Prop Bool
prop_translate e = evalI e =:= evalO (translate e)

