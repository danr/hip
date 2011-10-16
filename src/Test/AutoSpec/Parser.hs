{-# LANGUAGE TemplateHaskell #-}
module Test.AutoSpec.Parser where

import Prelude hiding (lex)
import Data.Parser.Grempa.Static
import Control.Applicative
import Test.AutoSpec.ParserInternals (extGrammar)
import Test.AutoSpec.Lexer
import Test.AutoSpec.Core

extTokParser :: [Tok] -> ParseResult Tok [ExtDecl]
extTokParser = $(mkStaticParser extGrammar [|extGrammar|])

extParser :: String -> ParseResult Tok [ExtDecl]
extParser = extTokParser . lex

parseFile :: String -> IO [ExtDecl]
parseFile n = either (error . show) return =<< extParser <$> readFile n