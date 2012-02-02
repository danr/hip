{-# LANGUAGE  RecordWildCards, ViewPatterns #-}
module Main where

import qualified Language.TPTP as T
import Language.TPTP.Pretty

import Autospec.FromHaskell.FromHaskell
import Autospec.ToFOL.ToTPTP
import Autospec.ToFOL.Pretty
import Autospec.ToFOL.ProofDatatypes
import Autospec.ToFOL.Parser
import Autospec.ToFOL.Core
import Autospec.ToFOL.Latex hiding (latex)
import Autospec.Util (groupSortedOn,concatMapM)
import Autospec.InvokeATPs
import Autospec.Messages
import Autospec.Provers
import Autospec.Params
import Autospec.ResultDatatypes

import System.Console.CmdArgs
import System.Exit (exitFailure,exitSuccess)
import System.IO

import Control.Monad
import Control.Monad.State
import Control.Applicative
import Control.Arrow

import Data.Function
import Data.Ord (comparing)
import Data.List
import Data.Maybe

import qualified Data.Map as M
import Data.Map (Map)

latexHeader' :: IO ()
latexHeader' = putStrLn $ unlines
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

latexFooter' :: IO ()
latexFooter' = putStrLn "\\end{document}"

outputSection :: Bool -> String -> IO ()
outputSection True  s = putStrLn $ "\\section*{" ++ s ++ "}"
outputSection False s = putStrLn $ s ++ ":"

outputSubSection :: Bool -> String -> IO ()
outputSubSection True  s = putStrLn $ "\\subsection*{" ++ s ++ "}"
outputSubSection False s = return ()

main :: IO ()
main = do
  params@Params{..} <- cmdArgs defParams
  when (null files) $ do
      putStrLn "No input files. Run with --help to see possible flags"
      exitFailure
  whenLoud $ putStrLn "Verbose output"
  when (latex && not tptp) $ latexHeader'
  total <- forM files $ \file -> do
      when (file /= head files) $ putStrLn ""
      when (length files > 1) $ outputSection latex file
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
      whenNormal $ when (not latex) $ mapM_ print (filter isWarning hsdebug)
      -- Output Core and terminate
      when core $ do mapM_ (putStrLn . prettyCore) ds
                     exitSuccess
      -- Don't prove anything, just dump translations
      if tptp then do
          -- Translation to FOL
          let (funcAxiomsWithDef,extraAxioms,debug) = dumpTPTP params ds
              axioms = extraAxioms ++ concatMap snd funcAxiomsWithDef
          -- Verbose output
          when dbfol $ mapM_ print (filter (sourceIs ToFOL) debug)
          -- Warnings
          whenNormal $ mapM_ print (filter isWarning debug)
          -- TPTP output
          if latex
            then do
              putStrLn (latexHeader file extraAxioms)
              mapM_ (putStr . uncurry latexDecl) funcAxiomsWithDef
              putStrLn latexFooter
              exitSuccess
            else do
              putStrLn (prettyTPTP axioms)
              exitSuccess
        else do
          -- Prove everything
          whenLoud $ putStrLn "Preparing proofs..."
          let (proofs,debug) = prepareProofs params ds
          -- Verbose output
          when dbfol   $ mapM_ print (filter (sourceIs ToFOL) debug)
          when dbproof $ mapM_ print (filter (sourceIs MakeProof) debug)
          -- Print warnings
          whenNormal $ when (not latex) $ mapM_ print (filter isWarning debug)
          whenLoud $ putStrLn "Done preparing proofs"
          proveAll latex processes timeout output reprove (proversFromString provers) file proofs
  return ()

echo :: Show a => IO a -> IO a
echo mx = mx >>= \x -> whenLoud (putStr (show x)) >> return x


proveAll :: Bool -> Int -> Int -> Maybe FilePath -> Bool -> [Prover]
         -> FilePath -> [Property]
         -> IO [PropResult]
proveAll latex processes timeout output reprove provers file properties = do
    whenLoud $ do putStrLn $ "Using " ++ show processes ++ " threads."
                  putStrLn $ "Timeout is " ++ show timeout
                  putStrLn $ "Output directory is " ++ show output
    hSetBuffering stdout LineBuffering

    let env = Env { reproveTheorems = reprove
                  , timeout         = timeout
                  , store           = output
                  , provers         = provers
                  , processes       = processes
                  , propStatuses    = error "main env propStatuses"
                  , propCodes       = error "main env propCodes"
                  }

    propRes <- invokeATPs properties env

    forM_ propRes $ \(Property propName propCode (status,parts)) -> do
         putStrLn $ propName ++ ": " ++ show status
         putStrLn propCode
         forM_ parts $ \part@(Part partMethod partCoverage particles) -> do
              putStrLn $ "  " ++ show partMethod ++ ": " ++ show (statusFromPart part)
              when (statusFromPart part > None) $ do
                  putStr "    "
                  forM_ particles $ \(Particle particleDesc (result,maybeProver)) ->
                       putStr $ particleDesc ++ ": " ++ show result ++
                                concat [ "[" ++ show prover ++ "]" | prover <- maybeToList maybeProver ]
                                ++ "  "
                  putStrLn ""
         putStrLn ""

    return propRes

pad :: Int -> String -> String
pad x s   = replicate (x - length s) ' '

latexCloseTabular :: IO ()
latexCloseTabular = putStrLn "\\end{longtable}"
