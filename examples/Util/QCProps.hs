module Main where

import System.IO
import System.Environment
import Data.List

main :: IO ()
main = do
  [f] <- getArgs
  c <- readFile f
  let out x = putStrLn $ "  quickCheck (printTestCase "
                         ++ show x ++ " " ++ x ++")"
  mapM_ out $ nub $ filter ((== "prop_") . take 5) (words c)



