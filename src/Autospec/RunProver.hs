module Autospec.RunProver where

import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent
import Control.Monad

import System.Process
import System.IO
import System.Exit
import Data.List

data ProverResult = Timeout | Theorem | Falsifiable | Unknown
  deriving (Eq,Ord)

instance Show ProverResult where
  show Timeout     = "timeout"
  show Theorem     = "ok"
  show Falsifiable = "false"
  show Unknown     = "?"

type Problem = (String,FilePath,String)
type Res     = (String,ProverResult)

runProvers :: Int -> Int -> Maybe FilePath -> [Problem] -> IO [Res]
runProvers processes timeout output problems = do
  probChan <- newChan
  mapM_ (writeChan probChan) problems
  resChan <- newChan
  ps <- replicateM processes $
             forkIO (worker timeout output probChan resChan)
  res <- getResults (length problems) resChan
  mapM_ killThread ps
  return res

getResults :: Int -> Chan Res -> IO [Res]
getResults 0 _  = return []
getResults n ch = do
    rest <- getResults (n-1) ch
    res  <- readChan ch
    rest `seq` return (res : rest)

worker :: Int -> Maybe FilePath -> Chan Problem -> Chan Res -> IO ()
worker timeout output probChan resChan = forever $ do
  (name,fname,str) <- readChan probChan
--   putStrLn $ "Working on " ++ name
  mvar <- newEmptyMVar
  pvar <- newEmptyMVar
  tid <- length str `seq` forkIO $ runProver str mvar pvar
  kid <- forkIO $ do threadDelay (timeout * 1000)
                     pid <- takeMVar pvar
                     killThread tid
                     terminateProcess pid
--                     putStrLn $ name ++ "killed"
                     putMVar mvar Timeout
  maybe (return ()) (\d -> writeFile (d ++ fname) str) output
  r <- takeMVar mvar
  killThread kid
  killThread tid
  writeChan resChan (name,r)

runProver :: String -> MVar ProverResult -> MVar ProcessHandle -> IO ()
runProver str mvar pvar = do
--    putStrLn "Running prover"

    let cmd = "eprover"
        args = words "-tAuto -xAuto --memory-limit=1000 --tptp3-format -s"

    (Just inh, Just outh, _, pid) <-
        createProcess (proc cmd args){ std_in  = CreatePipe,
                                       std_out = CreatePipe,
                                       std_err = Inherit }

    putMVar pvar pid

    -- fork off a thread to start consuming the output
    output  <- hGetContents outh
    outMVar <- newEmptyMVar
    _ <- forkIO $ length output `seq` putMVar outMVar ()

    -- now write and flush any input
    when (not (null str)) $ do hPutStr inh str; hFlush inh
    hClose inh -- done with stdin

    -- wait on the output
    takeMVar outMVar
    hClose outh

    -- wait on the process
    ex <- waitForProcess pid

    out <- case ex of
     ExitSuccess   -> return output
     ExitFailure r ->
       error ("readProcess: " ++ cmd ++
                                     ' ':unwords (map show args) ++
                                     " (exit " ++ show r ++ ")")


    let r | "Theorem" `isInfixOf` out            = Theorem
          | "Unsatisfiable" `isInfixOf` out      = Theorem
          | "CounterSatisfiable" `isInfixOf` out = Falsifiable
          | otherwise                            = Unknown
    putMVar mvar r

