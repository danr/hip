-- This module is only to be used for TPTP produced by the HFOL->TPTP tool
module Language.HFOL.Latex where

import Language.TPTP
import Data.List
import Data.Char
import Control.Monad.State
import Control.Applicative

runLatex :: Latex a => a -> String
runLatex = (++ "\\\\") . (`evalState` False) . latex

class Latex a where
  latex :: a -> State Bool String

instance Latex Decl where
  latex (Axiom _ phi)      = latex phi
  latex (Conjecture _ phi) = latex phi

quantifier :: Bool -> [VarName] -> Formula -> State Bool String
quantifier fa xs phi = do
  phi' <- latex phi
  return $ (if fa then " \\forall \\;" else " \\exists \\;")
         ++ intercalate " \\; " (map (map toLower . varName) xs)
         ++ " \\; . \\; " ++ phi'

eqop :: EqOp -> String
eqop (:==) = " = "
eqop (:!=) = " \\neq "

instance Latex EqOp where
  latex op = do
    b <- get
    put True
    if b then return (eqop op)
         else return (" & " ++ eqop op)

instance Latex BinOp where
  latex (:&) = return " \\wedge "
  latex (:|) = put True >> return "\\\\\n & \\vee "
  latex (:=>) = return " \\rightarrow "
  latex (:<=>) = return " \\leftrightarrow "

paren :: BinOp -> String -> String
paren (:=>) s = "(" ++ s ++ ")"
paren (:&)  s = "(" ++ s ++ ")"
paren _     s = s

-- | append for three arguments
trippend :: [a] -> [a] -> [a] -> [a]
trippend x y z = x ++ y ++ z

instance Latex Formula where
  latex (Forall xs phi) = quantifier True xs phi
  latex (Exists xs phi) = quantifier False xs phi
  latex (EqOp f1 op f2) = liftM3 trippend
                                 (latex f1)
                                 (latex op)
                                 (latex f2)
  latex (BinOp f1 (:=>) f2) = paren (:=>) <$> liftM3 trippend
                                                  (latex f2)
                                                  (return " \\leftarrow ")
                                                  (latex f1)
  latex (BinOp f1 op f2) = paren op <$> liftM3 trippend
                                               (latex f1)
                                               (latex op)
                                               (latex f2)
  latex (Neg f) = ("\\not" ++) <$> latex f
  latex (Rel r []) = return $ relName r
  latex (Rel r as) = do
    as' <- mapM latex as
    return (relName r ++ "(" ++ intercalate "," as' ++ ")")

showFunName :: FunName -> String
showFunName (FunName "Bottom") = "\\bot"
showFunName (FunName f)        = f

instance Latex Term where
  latex (Var x)    = return $ map toLower (varName x)
  latex (Fun f []) = return $ "\\mathrm{" ++ showFunName f ++ "}"
  latex (Fun f as) = do
    as' <- mapM latex as
    return ("\\mathrm{" ++ showFunName f ++ "}"
            ++ "(" ++ intercalate "," as' ++ ")")