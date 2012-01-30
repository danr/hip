{-# LANGUAGE RecordWildCards, ViewPatterns #-}
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
import Control.Monad.State
import Control.Monad.Trans
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent

import Data.List
import Data.Maybe

import qualified Data.Map as M
import Data.Map (Map)

--import qualified Data.Set as S
--import Data.Set (Set)

import Autospec.ToFOL.ProofDatatypes
import Autospec.ResultDatatypes
import Autospec.Provers
import Autospec.RunProver
import Language.TPTP.Pretty

type PropName = String

type PropResult = PropertyMatter (Status,[PartResult])
type PartResult = PartMatter [ParticleResult]
type ParticleResult = ParticleMatter (ProverResult,Maybe ProverName)

statusFromPart :: PartResult -> Status
statusFromPart (Part _ coverage (map (fst . particleMatter) -> res))
  = statusFromResults coverage res

data Env = Env { propStatuses    :: MVar (Map PropName Status)
               , propCodes       :: Map PropName String
               , reproveTheorems :: Bool
               , timeout         :: Int
               , store           :: Maybe FilePath
               , provers         :: [Prover]
               , processes       :: Int
               }

type ProveM = ReaderT Env IO

runProveM :: Env -> ProveM a -> IO a
runProveM = flip runReaderT

invokeATPs :: [Property] -> Env -> IO [PropResult]
invokeATPs properties env@(Env{..}) = do
    statusMVar <- newMVar M.empty
    let codes = M.fromList [ (probName,probCode) | Property probName probCode _ <- properties ]
        env' = env { propStatuses = statusMVar, propCodes = codes }
    probChan <- newChan
    resChan <- newChan
    let allParts = [ (probName,part) | Property probName _ parts <- properties , part <- parts ]
    mapM_ (writeChan probChan) allParts
    workers <- replicateM processes $ forkIO (runProveM env' (worker probChan resChan))
    res <- runProveM env' (listener (length allParts) resChan)
    mapM_ killThread workers
    return res

propStatus :: PropName -> ProveM Status
propStatus propName = do
    Env{..} <- ask
    if reproveTheorems
      then return None
      else do
        statusMap <- liftIO (readMVar propStatuses)
        let status = fromMaybe None (M.lookup propName statusMap)
--        liftIO $ putStrLn $ "status on " ++ propName ++ " is " ++ show status
        return status

updatePropStatus :: PropName -> Status -> ProveM ()
updatePropStatus propName status = do
    Env{..} <- ask
    unless reproveTheorems
       (liftIO $ modifyMVar_ propStatuses (return . M.insertWith min propName status))
--    liftIO $ do putStrLn $ "updated " ++ propName ++ " to " ++ show status
--                map <- readMVar propStatuses
--                print map

-- | Listens to all the results, report if a property was proven,
--   and puts them all in a list of results
listener :: Int -> Chan (PropName,PartResult) -> ProveM [PropResult]
listener parts resChan = do
    Env{..} <- ask
    fmap (makePropList propCodes) $ forM [1..parts] $ \_ -> do
        res@(propName,part@(Part _ _ resParticles)) <- liftIO (readChan resChan)
        let status = statusFromPart part
        updatePropStatus propName status
        return res
  where
    makePropList :: Map PropName String -> [(PropName,PartResult)] -> [PropResult]
    makePropList propCodeMap = M.elems . foldr (uncurry folder) M.empty
      where
        folder :: PropName -> PartResult -> Map PropName PropResult -> Map PropName PropResult
        folder name part = M.alter (Just . alterer) name
          where
            alterer :: Maybe PropResult -> PropResult
            alterer m = case m of
              Nothing -> Property name (propCodeMap M.! name) (statusFromPart part,[part])
              Just (Property name code (status,parts)) ->
                   Property name code (statusFromPart part `min` status,part:parts)

-- | A worker. Reads the channel of parts to process, and writes to
-- the result channel. Skips doing the rest of the particles if one
-- fails.  Not implemented: skipping a Part if another Part has
-- already proved this Property.
worker :: Chan (PropName,Part) -> Chan (PropName,PartResult) -> ProveM ()
worker partChan resChan = forever $ do
    (propName,Part partMethod partCoverage (partTheory,particles))  <- liftIO (readChan partChan)
    let theoryStr = prettyTPTP partTheory

    env@(Env{..}) <- ask

    let unnecessary Theorem       = True
        unnecessary FiniteTheorem = partCoverage == Finite
        unnecessary _             = False

    let processParticle :: Particle -> StateT Bool ProveM ParticleResult
        processParticle (Particle particleDesc particleAxioms) = do
            stop <- get
            if stop then return (Particle particleDesc (Failure,Nothing)) else do
                resvar <- liftIO newEmptyMVar
                let axiomsStr = theoryStr ++ "\n" ++ prettyTPTP particleAxioms

                length axiomsStr `seq`
                    (liftIO $ forkIO $ runProveM env $ runProvers axiomsStr resvar)

                case store of
                   Nothing  -> return ()
                   Just dir -> let filename = intercalate "_" [dir,propName,proofMethodFile partMethod,particleDesc] ++ ".tptp"
                               in  liftIO (writeFile (filename) theoryStr)

                (res,maybeProver) <- liftIO (takeMVar resvar)
                provedElsewhere <- unnecessary <$> lift (propStatus propName)

                when (not (success res) || provedElsewhere) (put True)
                return (Particle particleDesc (res,maybeProver))

    provedElsewhere <- unnecessary <$> propStatus propName

    res <- evalStateT (mapM processParticle particles) provedElsewhere

    liftIO (writeChan resChan (propName,Part partMethod partCoverage res))

runProvers :: String -> MVar (ProverResult,Maybe ProverName) -> ProveM ()
runProvers str res = do
    Env{..} <- ask
    liftIO . putMVar res =<< go provers
  where
    go (p:ps) = do t <- asks timeout
                   r <- liftIO $ runProver p str t
                   case r of
                      Failure   -> go ps
                      _         -> return (r,Just (proverName p))
    go []     = return (Failure,Nothing)


