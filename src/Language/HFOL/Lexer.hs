{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Language.HFOL.Lexer where

import Prelude hiding (lex)
import Data.Data
import Data.Char
import Data.Parser.Grempa.Static
import Language.Haskell.TH.Lift

data Tok = LPar | RPar
         | LBrace | RBrace
         | Eq | Arrow | Semi
         | Case | Of
         | UIdent { fromTok :: String }
         | LIdent { fromTok :: String }
  deriving (Show,Eq,Ord,Typeable,Data)

$(deriveLift ''Tok)

lident = LIdent ""
uident = UIdent ""

instance ToPat Tok where toPat = toConstrPat

lex :: String -> [Tok]
lex []           = []
lex ('(':xs)     = LPar   : lex xs
lex (')':xs)     = RPar   : lex xs
lex ('{':xs)     = LBrace : lex xs
lex ('}':xs)     = RBrace : lex xs
lex ('=':xs)     = Eq     : lex xs
lex ('-':'>':xs) = Arrow  : lex xs
lex (';':xs)     = Semi   : lex xs
lex ('c':'a':'s':'e':xs) = Case : lex xs
lex ('o':'f':xs)         = Of   : lex xs
lex s@(x:xs)
    | isLower x || x == '_' = lexIdent LIdent s
    | isUpper x = lexIdent UIdent s
    | isSpace x = lex xs
    | otherwise = error $ "lex failed on unknow character " ++ [x]

isIdentChar c = isAlphaNum c || c == '_'

lexIdent :: (String -> Tok) -> String -> [Tok]
lexIdent c s = let (i,s') = span isIdentChar s
               in  c i : lex s'
