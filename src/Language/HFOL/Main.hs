module Main where

import Language.TPTP.Pretty
import Language.HFOL.Parser
import Language.HFOL.ToTPTP

import Control.Monad

import System.Environment

main :: IO ()
main = do
  file:rest <- getArgs
  ds <- parseFile file
  let (formulas,debug) = toTPTP ds
  when ("-v" `elem` rest) (mapM_ putStrLn debug)
  putStrLn (prettyTPTP formulas)
