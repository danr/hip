{-# LANGUAGE TemplateHaskell #-}
module Language.HFOL.Parser where

import Prelude hiding (lex)
import Data.Parser.Grempa.Static
import Language.HFOL.ParserInternals (extGrammar)
import Language.HFOL.Lexer
import Language.HFOL.Core
import Language.HFOL.Pretty

extTokParser :: [Tok] -> ParseResult Tok [Decl]
extTokParser = $(mkStaticParser extGrammar [|extGrammar|])

extParser :: String -> ParseResult Tok [Decl]
extParser = extTokParser . lex

parseStringIO :: String -> IO ()
parseStringIO s = do
   case extParser s of
      Right r  -> mapM_ (putStrLn . prettyCore) r
      Left err -> do mapM_ print $ zip [0..] (lex s)
                     putStrLn (show err)

parseFile :: String -> IO [Decl]
parseFile n = do
   s <- readFile n
   case extParser s of
      Right r  -> return r
      Left err -> do mapM_ print $ zip [0..] (lex s)
                     error (n ++ " " ++ show err)
