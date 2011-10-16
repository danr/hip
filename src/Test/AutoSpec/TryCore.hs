module Main where

import Control.Applicative
import System.Environment
import Test.AutoSpec.Parser
import Test.AutoSpec.Pretty
import Test.AutoSpec.CompileCases

main = do
  file <- head <$> getArgs
  r <- parseFile file
  mapM_ (putStrLn . prettyCore) r
  putStrLn "\n---------------\n"
  mapM_ (putStrLn . prettyCore) (compileProg r)

