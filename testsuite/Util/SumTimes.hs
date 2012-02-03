module Main where

import Control.Arrow

import Data.List
import Data.Maybe
import System.Environment

main :: IO ()
main = do flags <- getArgs
          let incr | "-i" `elem` flags = 1
                   | otherwise         = 0
          let cactus = "-c" `elem` flags
          interact (header . table . sumTimes cactus incr . readTimes . rmComment)

table :: (Show a,Show b) => [(a,b)] -> String
table = unlines . map (\(a,b) -> show a ++ "\t" ++ show b)

header :: String -> String
header = ("time\tqty\n" ++)

rmComment :: String -> String
rmComment = unlines . drop 1 . lines

readTimes :: String -> [Integer]
readTimes = map ((`div` 1000) . read) . words

-- times are 0, 10 and so on in ms
-- incr is for log plots, then 0 needs to be 1
sumTimes :: Bool -> Int -> [Integer] -> [(Integer,Int)]
sumTimes True  _    xs = [ (t,length $ takeWhile (<= t) sorted) | t <- [0,10..maximum xs]]
  where
    sorted = sort xs

sumTimes False incr xs = [ (t,maybe 0 (incr+) (lookup t grps))
                         | t <- [0,10..maximum xs] ]
  where
    grps :: [(Integer,Int)]
    grps = (map (head &&& length) (group (sort xs)))
