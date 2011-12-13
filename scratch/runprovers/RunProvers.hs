module Main where

import System.Process
import System.IO
import System.Environment
import System.Timeout
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent
import Control.Exception
import System.Exit
import Control.Monad

main :: IO ()
main = go =<< getArgs

go :: [FilePath] -> IO ()
go [] = return ()
go (filename:fs) = do
    content <- readFile filename
    putStrLn $ filename ++ ":"
    res <- runProver content 100000
    putStrLn res
    putStrLn ""
    go fs

runProver :: String -> Int -> IO String
runProver input time = do
    let cmd = "eprover"
        args = words "-tAuto -xAuto --memory-limit=1000 --tptp3-format -s"

    (Just inh, Just outh, _, pid) <-
        createProcess (proc cmd args){ std_in  = CreatePipe,
                                       std_out = CreatePipe,
                                       std_err = Inherit }

    -- fork off a thread to start consuming the output
    output  <- hGetContents outh
    outMVar <- newEmptyMVar
    _ <- forkIO $ evaluate (length output) >> putMVar outMVar ()

    -- now write and flush any input
    when (not (null input)) $ do hPutStr inh input; hFlush inh
    hClose inh -- done with stdin

    done <- newEmptyMVar

    tid <- forkIO $ do
         -- read output
         takeMVar outMVar
         hClose outh
         return output
         -- wait on the process
         ex <- waitForProcess pid
         putMVar done (Just ex)

    kid <- forkIO $ do
         threadDelay time
         killThread tid
         terminateProcess pid
         ex <- waitForProcess pid -- getProcessExitCode pid
         putStrLn $ "Terminated, exit: " ++ show ex
--         when (ex == Nothing) $ putStrLn "warning: process still running!"
         putMVar done Nothing

    ex <- takeMVar done

    killThread tid
    killThread kid

    case ex of
       Nothing              -> return "# SZS status Timeout"
       Just ExitSuccess     -> return output
       Just (ExitFailure r) ->
           return ("runProver: " ++ input ++ " (exit " ++ show r ++ ")")



