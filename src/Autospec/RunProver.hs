{-# LANGUAGE RecordWildCards #-}
module Autospec.RunProver where

import Prelude hiding (catch)

import Autospec.ResultDatatypes
import Autospec.Provers

import Control.Concurrent

import Control.Exception
import Control.Monad

import System.Process
import System.IO
import System.Exit
import System.CPUTime

--import Data.List
--import Data.Maybe

runProver :: Prover -> String -> Int -> IO ProverResult
runProver (Prover{..}) inputStr timelimit = do
    (Just inh, Just outh, _, pid) <-
       createProcess (proc proverCmd (proverArgs timelimit))
                     { std_in  = CreatePipe
                     , std_out = CreatePipe
                     , std_err = Inherit }

    -- fork off a thread to start consuming the output
    output  <- hGetContents outh
    outMVar <- newEmptyMVar
    _ <- forkIO $ evaluate (length output) >> putMVar outMVar ()

    -- now write and flush any input
    when (not (null inputStr)) $ do hPutStr inh inputStr; hFlush inh
    hClose inh -- done with stdin

    timeStart <- getCPUTime

    exitCodeMVar <- newEmptyMVar

    tid <- forkIO $ do
         -- read output
         takeMVar outMVar
         hClose outh
         return output
         -- wait on the process
         ex <- waitForProcess pid
         putMVar exitCodeMVar (Just ex)

    kid <- forkIO $ do
         threadDelay (timelimit * 1000 * 1000)
         killThread tid
         terminateProcess pid
         ex <- waitForProcess pid
         putMVar exitCodeMVar Nothing

    maybeExitCode <- takeMVar exitCodeMVar

    timeStop <- getCPUTime

    let time = (timeStop - timeStart) `div` (1000*1000)

    killThread tid
    killThread kid

    return $ maybe Failure (const $ proverProcessOutput output time) maybeExitCode


