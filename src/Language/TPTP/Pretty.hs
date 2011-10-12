{-# LANGUAGE FlexibleInstances, TemplateHaskell
 #-}
module Language.TPTP.Pretty where

import Language.TPTP
import Data.List

class Pretty p where
    pretty :: p -> String

instance Pretty FunName where
    pretty = show

instance Pretty RelName where
    pretty = show

instance Pretty VarName where
    pretty = show

csv :: Pretty a => [a] -> String
csv = intercalate "," . map pretty

argList :: Pretty a => [a] -> String
argList [] = ""
argList xs = paren (csv xs)

bindList :: Pretty a => [a] -> String
bindList [] = error "Empty bind list"
bindList xs = "[" ++ csv xs ++ "]"

paren :: String -> String
paren s = "(" ++ s ++ ")"

instance Pretty Term where
    pretty (Fun f args) = pretty f ++ argList args
    pretty (Var x)      = pretty x

instance Pretty BinOp where
    pretty (:&)   = " & "
    pretty (:|)   = " | "
    pretty (:=>)  = " => "
    pretty (:<=>) = " <=> "

instance Pretty Formula where
    pretty (EqOp t1 (:==) t2) = pretty t1 ++ " = " ++  pretty t2
    pretty (EqOp t1 (:!=) t2) = pretty t1 ++ " != " ++  pretty t2
    pretty (Rel r args)     = pretty r ++ argList args
    pretty (Neg f)          = "~ " ++ paren (pretty f)
    pretty (BinOp f1 op f2) = paren (pretty f1) ++ pretty op ++ paren (pretty f2)
    pretty (Forall vs f)    = "! " ++ bindList vs ++ ": " ++ paren (pretty f)
    pretty (Exists vs f)    = "? " ++ bindList vs ++ ": " ++ paren (pretty f)

pdecl :: String -> String -> Formula -> String
pdecl n t f = "fof" ++ paren (n ++ "," ++ t ++ "," ++ pretty f) ++ "."

instance Pretty Decl where
    pretty (Axiom      n f) = pdecl n "axiom"      f
    pretty (Conjecture n f) = pdecl n "conjecture" f

instance Pretty [Decl] where
    pretty ds = unlines (map pretty ds)

writeTPTP :: Pretty a => FilePath -> a -> IO ()
writeTPTP file a = writeFile file (pretty a)

outputTPTP :: Pretty a => a -> IO ()
outputTPTP = putStr . pretty
