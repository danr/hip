module Main where

import System.Process
import System.IO
import System.Environment
import System.Timeout
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent

main :: IO ()
main = do
    files <- getArgs
    go files
    return ()

go :: [FilePath] -> IO ()
go [] = return ()
go (filename:fs) = do
--    resMVar <- newEmptyMVar
    content <- readFile filename
    res <- timeout 100000 (runProver content)
--    res <- readMVar resMVar
    putStrLn filename
    case res of Nothing  -> putStrLn "Status: Timeout"
                Just out -> putStrLn out
    putStrLn ""
    go fs

runProver :: String -> IO String
runProver inp = do
   let cmd = "eprover"
       args = words "-tAuto -xAuto --memory-limit=1000 --tptp3-format -s"
   readProcess cmd args inp



