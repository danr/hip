{-# LANGUAGE TemplateHaskell #-}
module Test.AutoSpec.Parser where

import Prelude hiding (lex)
import Data.Parser.Grempa.Static
import Test.AutoSpec.ParserInternals (extGrammar)
import Test.AutoSpec.Lexer
import Test.AutoSpec.Core
import Test.AutoSpec.Pretty

extTokParser :: [Tok] -> ParseResult Tok [ExtDecl]
extTokParser = $(mkStaticParser extGrammar [|extGrammar|])

extParser :: String -> ParseResult Tok [ExtDecl]
extParser = extTokParser . lex

parseFile :: String -> IO () -- [ExtDecl]
parseFile n = do
   s <- readFile n
   case extParser s of
      Right r  -> mapM_ (putStrLn . prettyCore) r
      Left err -> do mapM_ print $ zip [0..] (lex s) 
                     error (show err)
