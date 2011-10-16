{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Test.AutoSpec.Lexer where

import Prelude hiding (lex)    
import Data.Data
import Data.Char
import Data.Parser.Grempa.Static
import Language.Haskell.TH.Lift

data Tok = LPar | RPar
         | LBrace | RBrace
         | Eq | Arrow | Semi | Under
         | Case | Of | Fail
         | UIdent { fromTok :: String }
         | LIdent { fromTok :: String }
  deriving (Show,Eq,Ord,Typeable,Data)

$(deriveLift ''Tok)

instance ToPat Tok where toPat = toConstrPat

lex :: String -> [Tok]
lex [] = []
lex ('(':xs) = LPar : lex xs
lex (')':xs) = RPar : lex xs
lex ('{':xs) = LBrace : lex xs
lex ('}':xs) = RBrace : lex xs
lex ('=':xs) = Eq : lex xs
lex ('-':'>':xs) = Arrow : lex xs
lex (';':xs) = Semi : lex xs
lex ('_':xs) = Under : lex xs
lex ('c':'a':'s':'e':xs) = Case : lex xs
lex ('o':'f':xs) = Of : lex xs
lex ('f':'a':'i':'l':xs) = Fail : lex xs
lex s@(x:xs)
    | isLower x = lexIdent LIdent s
    | isUpper x = lexIdent UIdent s
    | isSpace x = lex xs
    | otherwise = error $ "lex failed on unknow character " ++ [x]

isIdentChar c = isAlphaNum c || c == '_'

lexIdent :: (String -> Tok) -> String -> [Tok]
lexIdent c s = let (i,s') = span isIdentChar s
               in  c i : lex s'
                                  