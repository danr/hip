module Hip.Trans.Property where

import Hip.Trans.Theory
import Hip.Trans.SrcRep

import CoreSyn
import Var

import Halt.Utils

trProperty :: CoreBind -> Prop
trProperty (NonRec prop_name e) =
    let (_,vars,e') = collectTyAndValBinders e

        (lhs,rhs) = case collectArgs e' of
                       (Var x,[l,r]) | isEquals x    -> (l,r)
                       (Var x,[l])   | isProveBool x -> (l,Var trueDataConId)
                       _  -> error "trProperty, not a prooperty!"

    in  Prop { propName = idToStr prop_name
             , proplhs  = lhs
             , proprhs  = rhs
             , propVars = [ (x,varType x) | x <- vars ]
             , propRepr = showExpr lhs ++ " = " ++ showExpr rhs
             , propQSTerms = error "trProperty : propQSTerms"
             }
