{-# LANGUAGE RecordWildCards #-}
module Autospec.InvokeATPs where

-- These environment parameters should be configurable run-time for
-- the GUI front end

-- Add a hook when something succeeds/fails so the GUI can be updated
-- and also verbose mode in terminal

-- Flag for extequality and appbottom

-- particle id:s,good or bad idea? how else to handle this
-- I know it's not very functional, but it might at least function ^^


-- Environment
-- particles and where they come from based on IDs
-- provers to use
-- timeout
-- store directory
-- how to describe a particle?
-- abandon parts (why wouldn't we want this?)
--    actually we always want to do this:
--    only measure the time on successes when testing a prover,
--    not on non-theorems (this wouldn't be so interesting)

-- structural induction and fixpoint induction filenames? especially tricky
-- strind should be on constructors (almost like that now)
-- fixpoint induction should be on the functions + permutation int maybe

-- provers list from the environment
-- two alternatives here for exhaustive test:
-- try all provers and report which worked
-- this is not great since it is hard to combine the results from different particles
-- another attempt to view differences between different provers is to
-- run an invocation on the test suite for each prover
-- and report how much succeeded, and maybe some statistics on avg, median, max, min
-- time on successes. histogram maybe?! :D


import System.CPUTime

import Control.Monad
import Control.Applicative
import Control.Monad.Reader
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent

import Data.IORef

import qualified Data.Map as M
import Data.Map (Map)

import qualified Data.Set as S
import Data.Set (Set)

import Autospec.ResultDatatypes

type PropName = String

type PartResult = PartMatter [Principle ProverResult]

type PropResult = PropertyMatter [(ProverRes,PartResult)]

data Env = Env { timeout         :: Int
               , store           :: Maybe FilePath
               , provedProps     :: MVar (Set PropName)
               , propCodes       :: Map PropName String
               , reproveTheorems :: Bool
               , provers         :: [Prover]
               , processes       :: Int
               }

type ProveM = ReaderT Env IO

runProveM :: Env -> ProveM a -> a
runProveM = flip runReaderT

invokeATPs :: [Property] -> Env -> IO [PropResult]
invokeATPs properties env@(Env{..}) = do
    probChan <- newChan
    resChan <- resChan
    sequence_ [ writeChan probChan (probName,part) | Property probName _ part <- properties ]
    workers <- replicateM processes $ forkIO (runProveM env (worker probChan resChan))
    res <- runProveM env (listener resChan)
    mapM_ killThread workers
    return res

propProved :: PropName -> ProveM Bool
propProved propName = do
    Env{..} <- ask
    if reproveTheorems
      then return False
      else do
        proved <- readMVar provedProps
        return (propName `S.member` proved)

setPropProved :: PropName -> ProveM Bool
setPropProved propName = do
    Env{..} <- ask
    unless reproveTheorems (modifyMVar_ provedProps (S.insert propName))

-- | Listens to all the results, report if a property was proven,
--   and puts them all in a list of results
listener :: Int -> Chan (PropName,PartResult) -> ProveM [PropResult]
listener parts resChan = do
    Env{..} <- ask
    fmap (makePropList propCodes) $ forM_ [1..parts] $ \_ -> do
        t@(_,(Part _ _ resParticles)) <- readChan rpesChan
        let res = flattenProverResults (map principleMatter resParticles)
        when (success res) $ setPropProved propName
        return t
  where
    makePropList :: Map PropName String -> [(PropName,PartResult)] -> [PropResult]
    makePropList propCodeMap = M.elems . foldr (uncurry folder) M.empty
      where
        folder :: PropName -> PartResult -> Map PropName PropResult -> Map PropName PropResult
        folder name partRes = M.alter (Just . alterer) name
          where
            alterer :: Maybe PropResult -> PropResult
            alterer Nothing                              = Property name (propCodeMap M.! name) (partRes,[partRes])
            alterer (Just (Property name code partsRes)) = Property name code (disjoinProverResults newRes,newRes)
              where newRes = partRes:partsRes

-- | A worker. Reads the channel of parts to process, and writes to
-- the result channel. Skips doing the rest of the particles if one
-- fails.  Not implemented: skipping a Part if another Part has
-- already proved this Property.
worker :: Chan (PropName,Part) -> Chan (PropName,PartResult) -> ProveM ()
worker partChan resChan = forever $ do
    (propName,Part partMethod partCoverage (partTheory,particles))  <- readChan partChan
    let theoryStr = prettyTPTP partTheory

    env@(Env{..}) <- ask

    alreadyProved <- propProved propName

    res <- (`evalStateT` alreadyProved)
         $ forM particles $ \(Particle particleDesc particleAxioms) -> do
               failed <- get
               if failed
                 then return (Particle particleDesc Failure)
                 else do
                   resvar <- newEmptyMVar
                   let axiomsStr = theoryStr ++ "\n" ++ prettyTPTP particleAxioms

                   length axiomsStr `seq`
                       (liftIO $ forkIO $ runProveM env $ runProvers axiomsStr resvar)

                   case store of
                      Nothing  -> return ()
                      Just dir -> let fname = intercalate "_" [dir,propName,proofMethodFile partMethod,particleDesc] ++ ".tptp"
                                  in  liftIO $ writeFile (fp ++ filename) theoryStr

                   res <- takeMVar resvar
                   provedElsewhere <- lift (propProved propName)

                   when (not (success res) || provedElsewhere) (put True)
                   return (Particle particleDesc res)

    writeChan resChan (Part partMethod partCoverage res,propName)

runProvers :: String -> MVar resvar -> ProverM ()
runProvers str res = do
    Env{..} <- ask
    putMVar res =<< go provers
  where
    go (p:ps) = do t <- asks timeout
                   r <- liftIO $ runProver p str t
                   case r of
                      Failure   -> go ps
                      _         -> return r
    go []     = Failure


-- timeout from some environment
runProver :: Prover -> String -> Int -> IO ProverResult
runProver (Prover{..}) inputStr timelimit = do
    (Just inh, Just outh, _, pid) <-
       createProcess (proc proverCmd (proverArgs timelimit)
                     { std_in  = CreatePipe
                     , std_out = CreatePipe
                     , std_err = Inherit })

    -- fork off a thread to start consuming the output
    output  <- hGetContents outh
    outMVar <- newEmptyMVar
    _ <- forkIO $ evaluate (length output) >> putMVar outMVar ()

    -- now write and flush any input
    when (not (null input)) $ do hPutStr inh inputStr; hFlush inh
    hClose inh -- done with stdin

    timeStart <- getCPUTime

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
         threadDelay timelimit
         killThread tid
         terminateProcess pid
         ex <- waitForProcess pid
         putMVar done Nothing

    ex <- takeMVar done

    timeStop <- getCPUTime

    let time = (timeStop - timeStart) `div` (1000*1000*1000)

    killThread tid
    killThread kid

    return $ case ex of
               Nothing              -> Failure
               Just ExitSuccess     -> proverProcessOutput output time
               Just (ExitFailure r) -> Unknown (output ++ "\n(exit " ++ show r ++ ")")

