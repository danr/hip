module Main where

import qualified Language.TPTP as T
import Language.TPTP.Pretty

import Language.HFOL.FromHaskell.FromHaskell
import Language.HFOL.ToFOL.ToTPTP
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.ToFOL.Parser
import Language.HFOL.ToFOL.Latex
import Language.HFOL.ToFOL.Core

import System.Environment (getArgs)
import System.Exit (exitFailure,exitSuccess)

import Control.Monad (when)
import Control.Applicative ((<$>))
import Data.List (isSuffixOf)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> printUsage
    file:flags -> do
      let flag = (`elem` flags)
      -- Parse either Haskell or Core
      (eitherds,hsdebug) <- if "hs" `isSuffixOf` file
                                then parseHaskell <$> readFile file
                                else flip (,) []  <$> parseFile file
      ds <- either (\estr -> putStrLn estr >> exitFailure) return eitherds
      -- Output debug of translation
      when (flag "-d") (mapM_ putStrLn hsdebug)
      -- Output Core
      when (flag "-c" || flag "-ct") (mapM_ (putStrLn . prettyCore) ds)
      -- Output Core and terminate
      when (flag "-ct") exitSuccess
      -- Translation to FOL
      let (funcAxiomsWithDef,extraAxioms,debug) = toTPTP ds
          axioms = extraAxioms ++ concatMap snd funcAxiomsWithDef
      -- Verbose output
      when (flag "-v") (mapM_ putStrLn debug)
      -- TPTP output
      when (flag "-t" || not (flag "-l")) (putStrLn (prettyTPTP axioms))
      -- Latex output
      when (flag "-l") $ do
          putStrLn (latexHeader file extraAxioms)
          mapM_ (putStr . uncurry latexDecl) funcAxiomsWithDef
          putStrLn latexFooter

printUsage :: IO ()
printUsage = mapM_ putStrLn
  [ "Usage:"
  , "First argument is filename"
  , "    suffix: hs then it is assumed to be haskell"
  , "    other suffix is Core"
  , "Flags:"
  , "-d    show debug from Haskell->Core translation"
  , "-c    output Core"
  , "-ct   output Core and terminate"
  , "-v    verbose output of Core->FOL translation"
  , "-t    output TPTP (default, supressed with latex output)"
  , "-l    output FOL as Latex"
  ]



