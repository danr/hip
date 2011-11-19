{-# LANGUAGE TemplateHaskell #-}
module Autospec.ToFOL.Parser where

import Prelude hiding (lex)
import Data.Parser.Grempa.Static
import Autospec.ToFOL.ParserInternals (declsGrammar)
import Autospec.ToFOL.Lexer
import Autospec.ToFOL.Core
import Autospec.ToFOL.Pretty

extTokParser :: [Tok] -> ParseResult Tok [Decl]
extTokParser = $(mkStaticParser declsGrammar [|declsGrammar|])

extParser :: String -> ParseResult Tok [Decl]
extParser = extTokParser . lex

parseStringIO :: String -> IO ()
parseStringIO s =
   case extParser s of
      Right r  -> mapM_ (putStrLn . prettyCore) r
      Left err -> do mapM_ print $ zip [(0 :: Integer)..] (lex s)
                     print err

parseFile :: String -> IO (Either String [Decl])
parseFile n = do
   s <- readFile n
   case extParser s of
      Right r  -> return (Right r)
      Left err -> return (Left (unlines
                     (map show (zip [(0 :: Integer)..] (lex s))
                       ++ [n ++ " " ++ show err])))
