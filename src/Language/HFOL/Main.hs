module Main where

import Language.TPTP.Pretty
import Language.HFOL.Parser
import Language.HFOL.ToTPTP

import System.Environment

main = do
  file:_ <- getArgs
  ds <- parseFile file
  putStrLn (prettyTPTP (toTPTP ds))