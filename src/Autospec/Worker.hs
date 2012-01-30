-- Sketch of how run provers should be redesigned


import System.CPUTime

import Control.Monad
import Control.Applicative
--import Control.Monad.
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent

import qualified Data.Map as M
import Data.Map (Map)

import qualified Data.Set as S
import Data.Set (Set)

import Autospec.ResultDatatypes

type ParticleID = Int

type PropertyV  = PropertyMatter ()
type PartV      = PartMatter ()
type PrincipleV = PrincipleMatter ()

-- Make unique id for each property and part
work :: [Property] -> IO
work =

makeIDs :: [Property] -> ..
makeIDs []     = ...
makeIDs (p:ps) =

{- Points upwards, example


property               +-assoc----
                        -- --     \-----
                      -/     \--        \-----
                    -/          \-            \--
part             strind           approx       fpi-1         ...
                  / |  \             |          /  \
                 /  |   \            |         /    \
                /   |    \           |        /      |
principle     _|_   S     Z        step       base step



-}
type Tree = Map Unique Unique

data Env = Env { tree            :: True
               , lookupProperty  :: Map Unique Property
               , lookupPart      :: Map Unique Part
               , lookupPrinciple :: Map Unique Principle
               }

makeUniqueIDs :: [Part] -> ReaderT (Env,Set Name) IO Env
makeUniqueIDs [] = fst =<< ask
makeUniqueIDs (Part{..}:ps) = do
    (e,s) <- ask




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

worker :: Chan [Particle] -> Chan (Particle,PartResult) -> IO ()
worker particleChan resChan = forever $ do
    particleID  <- readChan        particleChan
    proceed     <- proceedParticle particleID
    unless (partAbandoned && abandonParts) $ do
        resvar <- newEmptyMVar
        tptpTheory <- getTPTPTheory particleID
        length tptpTheory `seq` forkIO (runProvers tptpTheory resvar)
        filename <- getFilename particleID
        when store $ writeFile filename tptpTheory
        res <- takeMVar resvar
        writeChan resChan (particleID,res)


-- provers list from the environment
-- two alternatives here for exhaustive test:
-- try all provers and report which worked
-- this is not great since it is hard to combine the results from different particles
-- another attempt to view differences between different provers is to
-- run an invocation on the test suite for each prover
-- and report how much succeeded, and maybe some statistics on avg, median, max, min
-- time on successes. histogram maybe?! :D
runProvers :: String -> MVar resvar -nnnn> IO ()
runProvers str res = putMVar res =<< go provers
  where
    go (p:ps) = do r <- runProver p str
                   case r of
                      Failure   -> go ps
                      _         -> return r
    go []     = Failure


-- timeout from some environment
runProver :: Prover -> String -> IO ProverResult
runProver (Prover{..}) inputStr = do
    (Just inh, Just outh, _, pid) <-
    createProcess (proc proverCmd (proverArgs timeout))
                  { std_in  = CreatePipe
                  , std_out = CreatePipe
                  , std_err = Inherit }

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
         threadDelay time
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



