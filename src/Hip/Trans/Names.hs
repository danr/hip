module Hip.Trans.Names where

import Hip.Trans.Core

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)

projName :: Int -> Name
projName i = "proj" ++ show i

projExpr :: Int -> Expr -> Expr
projExpr i e = App (projName i) [e]

proj :: Int -> Term -> Term
proj i t = Fun (FunName (projName i)) [t]
