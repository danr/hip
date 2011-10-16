module Main where

import System.Environment
import Test.AutoSpec.Parser

main = mapM_ parseFile =<< getArgs 