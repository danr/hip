module Main where

import System.Environment
import Data.List
import Control.Monad
import Control.Applicative

main = do
    files' <- getArgs
    putStrLn header
    case files' of
       -- Only print total summary
       "-t":files -> do
           putStrLn $ unlines [section "Total",beginTabular statWidths,captions]
           forM_ files $ \file -> do
               total <- last . lines <$> readFile file
               let totalWithFile = fixName file ++ dropWhile (/= '&') total
               putStrLn $ totalWithFile ++ "\\\\"
           putStrLn endTabular

       -- Concats full summary
       files -> forM_ files $ \file -> do
           putStrLn $ unlines [section (fixName file),beginTabular statWidths,captions]
           rows <- readFile file
           putStrLn $ unlines $ map (++ "\\\\")  $ drop 2 $ lines rows
           putStrLn endTabular
    putStrLn footer
  where
    fixName name = [ if c == '/' || c == '_' then ' ' else c | c <- name ]

header :: String
header = unlines
  [ "\\documentclass{article}"
  , "\\usepackage{fullpage}"
  , "\\usepackage{courier}"
  , "\\usepackage{amssymb}"
  , "\\usepackage{longtable}"
  , ""
  , "\\begin{document}"
  , ""
  , "\\title{Results}"
  , "\\maketitle"
  ]

footer :: String
footer = "\\end{document}"

section :: String -> String
section s = "\\section*{" ++ s ++ "}"


statWidths :: [String]
statWidths = ["l","||"] ++ intersperse "|" (replicate 5 "c")
              ++ ["||"] ++ intersperse "|" (replicate 2 "c")


captions :: String
captions = " & Theorem & plain & ind & approx & fixpoint & Finite & ind \\\\"

beginTabular :: [String] -> String
beginTabular widths = "\\begin{longtable}{" ++ unwords widths ++ "}"

endTabular :: String
endTabular = "\\end{longtable}"
