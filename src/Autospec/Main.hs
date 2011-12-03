{-# LANGUAGE DeriveDataTypeable, RecordWildCards, ViewPatterns #-}
module Main where

import qualified Language.TPTP as T
import Language.TPTP.Pretty

import Autospec.FromHaskell.FromHaskell
import Autospec.ToFOL.ToTPTP
import Autospec.ToFOL.Pretty
import Autospec.ToFOL.ProofDatatypes
import Autospec.ToFOL.Parser
import Autospec.ToFOL.Latex hiding (latex)
import Autospec.Util (groupSortedOn)
import Autospec.RunProver
import Autospec.Messages

import System.Console.CmdArgs
import System.Exit (exitFailure,exitSuccess)
import System.IO

import Control.Monad
import Control.Applicative
import Data.Function
import Data.Ord (comparing)
import Data.List (isSuffixOf,groupBy,find,sortBy,genericLength)

data Params = Params { files     :: [FilePath]
                     , processes :: Int
                     , output    :: Maybe FilePath
                     , timeout   :: Int
                     , latex     :: Bool
                     , tptp      :: Bool
                     , core      :: Bool
                     , dbfh      :: Bool
                     , dbfol     :: Bool
                     , dbproof   :: Bool
                     }
  deriving (Show,Data,Typeable)

params :: Params
params = Params
  { files     = []      &= args &= typFile
  , processes = 4       &= help "Number of prover processes (default 4)"
  , output    = Nothing &= opt  "proving/" &= typDir
                        &= help "Output all tptp files in a directory (default proving/)"
  , timeout   = 500     &= help "Timout of provers in milliseconds (default 500)" &= name "t"
  , latex     = False   &= help "Generate latex output and terminate"
  , tptp      = False   &= help "Generate tptp output and terminate" &= name "f"
  , core      = False   &= help "Translate hs to core and terminate"
  , dbfh      = False   &= help "Print debug output of Haskell -> Core translation"
  , dbfol     = False   &= help "Print debug output of Core -> FOL"
  , dbproof   = False   &= help "Print debug output when making proofs"
  }
  &= summary "autospec v0.1 Dan Rosén danr@student.gu.se"
  &= program "autospec"
  &= verbosity

main :: IO ()
main = do
  Params{..} <- cmdArgs params
  when (null files) $ do
      putStrLn "No input files. Run with --help to see possible flags"
      exitFailure
  whenLoud $ putStrLn "Verbose output"
  forM_ files $ \file -> do
      when (length files > 1) $ putStrLn file
      -- Parse either Haskell or Core
      (eitherds,hsdebug) <- if "hs" `isSuffixOf` file
                                then parseHaskell <$> readFile file
                                else flip (,) []  <$> parseFile file
      ds <- either (\estr -> putStrLn estr >> exitFailure) return eitherds
      -- Output debug of translation
      when dbfh $ do
        putStrLn "Translating from Haskell..."
        mapM_ print (filter (sourceIs FromHaskell) hsdebug)
        putStrLn "Translation from Haskell translation complete."
      -- Output warnings of translation
      whenNormal $ mapM_ print (filter isWarning hsdebug)
      -- Output Core and terminate
      when core $ do mapM_ (putStrLn . prettyCore) ds
                     exitSuccess
      -- Don't prove anything, just dump translations
      if tptp || latex then do
          -- Translation to FOL
          let (funcAxiomsWithDef,extraAxioms,debug) = dumpTPTP ds
              axioms = extraAxioms ++ concatMap snd funcAxiomsWithDef
          -- Verbose output
          when dbfol $ mapM_ print (filter (sourceIs ToFOL) debug)
          -- Warnings
          whenNormal $ mapM_ print (filter isWarning debug)
          -- TPTP output
          when tptp $ do putStrLn (prettyTPTP axioms)
                         exitSuccess
          -- Latex output
          when latex $ do
              putStrLn (latexHeader file extraAxioms)
              mapM_ (putStr . uncurry latexDecl) funcAxiomsWithDef
              putStrLn latexFooter
              exitSuccess
        else do
          -- Prove everything
          whenLoud $ putStrLn "Preparing proofs..."
          let (proofs,debug) = prepareProofs ds
          -- Verbose output
          when dbfol   $ mapM_ print (filter (sourceIs ToFOL) debug)
          when dbproof $ mapM_ print (filter (sourceIs MakeProof) debug)
          -- Print warnings
          whenNormal $ mapM_ print (filter isWarning debug)
          whenLoud $ putStrLn "Done preparing proofs"
          proveAll processes timeout output file proofs

echo :: Show a => IO a -> IO a
echo mx = mx >>= \x -> whenLoud (putStr (show x)) >> return x

proveAll :: Int -> Int -> Maybe FilePath
         -> FilePath -> [ProofDecl] -> IO ()
proveAll processes timeout output file proofs = do
    whenLoud $ do putStrLn $ "Using " ++ show processes ++ " threads."
                  putStrLn $ "Timeout is " ++ show timeout
                  putStrLn $ "Output directory is " ++ show output
    hSetBuffering stdout NoBuffering
    res <- runProvers processes timeout output (map (fmap prettyTPTP) proofs)
    let resgroups :: [[Res]]
        resgroups = groupSortedOn principleName res
    whenNormal $ forM_ resgroups $ \grp@(Principle name _ _ _ _:_) -> do
        let Just (Principle _ _ _ pstr _) = find ((name ==) . principleName) proofs
        putStrLn $ "\n" ++ name
        putStrLn $ pstr
        putStrLn $ "Status: " ++ show (statusFromGroup grp)
        forM_ grp $ \(Principle name ptype res _ parts) -> do
             putStrLn $ "    " ++ show ptype ++ ": " ++ show res
             putStr "        "
             forM_ parts $ \(Part pname pres _) ->
                 putStr $ pname ++ ": " ++ show pres ++ " "
             putStrLn ""
    -- Statistics
    -- Theorems/FiniteTheorems/All
    whenNormal $ putStrLn ""
    let proverres = groupSortedOn statusFromGroup resgroups
        n         = genericLength resgroups :: Double
        pad x s   = replicate (x - length s) ' '
    forM_ proverres $ \pgrp@(grp:_) -> do
         let res = statusFromGroup grp
         putStrLn $ show res
                 ++ ":" ++ pad 18 (show res) ++ show (length pgrp)
                 ++ "\t(" ++ take 5 (show (genericLength pgrp / n * 100)) ++ "%)"
