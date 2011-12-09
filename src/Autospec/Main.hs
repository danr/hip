{-# LANGUAGE DeriveDataTypeable, RecordWildCards, ViewPatterns #-}
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
import Autospec.RunProver
import Autospec.Messages
import Autospec.Results

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
  Params{..} <- cmdArgs params
  when (null files) $ do
      putStrLn "No input files. Run with --help to see possible flags"
      exitFailure
  whenLoud $ putStrLn "Verbose output"
  when latex $ latexHeader'
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

          return undefined
        else do
          -- Prove everything
          whenLoud $ putStrLn "Preparing proofs..."
          let (proofs,debug) = prepareProofs ds
          -- Verbose output
          when dbfol   $ mapM_ print (filter (sourceIs ToFOL) debug)
          when dbproof $ mapM_ print (filter (sourceIs MakeProof) debug)
          -- Print warnings
          whenNormal $ when (not latex) $ mapM_ print (filter isWarning debug)
          whenLoud $ putStrLn "Done preparing proofs"
          proveAll latex processes timeout output file proofs
  let rgs :: [(Result,ResGroup)]
      (rgs,ns) = first concat $ unzip total
      rgr :: [(Result,ResGroup)]
      rgr = map (fst . head &&& flattenGroups . map snd)
          $ groupSortedOn fst rgs
      n  = sum ns

  when (length files > 1) $ do
    outputSection latex "Total Summary"
    when latex (outputGroupLatexHeader True)
    forM_ rgr $ \(r,rgs) -> outputResGroup latex n r rgs
    when latex latexCloseTabular

  when latex latexFooter'

echo :: Show a => IO a -> IO a
echo mx = mx >>= \x -> whenLoud (putStr (show x)) >> return x

data ResGroup = ResGroup (Map ProofType Int) Int
    deriving (Eq,Ord,Show)

flattenGroups :: [ResGroup] -> ResGroup
flattenGroups [] = ResGroup M.empty 0
flattenGroups (ResGroup m x:xs) =
   let ResGroup m' t = flattenGroups xs
   in  ResGroup (M.unionWith (+) m m') (x + t)

proveAll :: Bool -> Int -> Int -> Maybe FilePath
         -> FilePath -> [ProofDecl]
         -> IO ([(Result,ResGroup)],Int)
proveAll latex processes timeout output file proofs = do
    whenLoud $ do putStrLn $ "Using " ++ show processes ++ " threads."
                  putStrLn $ "Timeout is " ++ show timeout
                  putStrLn $ "Output directory is " ++ show output
    hSetBuffering stdout NoBuffering
    res <- runProvers processes timeout output (map (fmap prettyTPTP) proofs)
    let resgroups :: [[Res]]
        resgroups = groupSortedOn principleName res
    whenNormal $ do
        outputSubSection latex "Properties"
        when latex (outputGroupLatexHeader False)
        forM_ resgroups $ \grp@(Principle name _ _ _ _:_) -> do
           let Just (Principle _ _ _ pstr _) = find ((name ==) . principleName) proofs
           outputGroup latex name pstr (statusFromGroup grp) grp
        when latex latexCloseTabular
    -- Statistics
    -- Theorems/FiniteTheorems/All
    whenNormal $ putStrLn ""
    let proverres :: [[[Res]]]
        proverres = groupSortedOn statusFromGroup resgroups
        n         = length resgroups
    outputSubSection latex "Summary"
    when latex (outputGroupLatexHeader True)
    r <- flip concatMapM proverres $ \pgrp@(grp:_) -> do
            let res = statusFromGroup grp
            if res == None
                then return []
                else do
                    let tot = length pgrp
                        rg = ResGroup (stats pgrp res) tot
                    outputResGroup latex n res rg
                    return [(res,rg)]
    when latex latexCloseTabular
    return (r,n)

pad :: Int -> String -> String
pad x s   = replicate (x - length s) ' '

stats :: [[Res]] -> Result -> Map ProofType Int
stats ress r = execState (mapM_ statFromProp ress)
                         (M.fromList (zip proofTypes (repeat 0)))
  where
    -- All these come from the same property
    statFromProp :: [Res] -> State (Map ProofType Int) ()
    statFromProp res = forM_ proofTypes $ \pt -> do
        let y = any (\(Principle _ pt' r' _ _) ->
                    pt' `liberalEq` pt && r == r') res
        when y $ modify (M.adjust succ pt)

outputGroupLatexHeader :: Bool -> IO ()
outputGroupLatexHeader total = do
    putStrLn $ "\\begin{longtable}{p{" ++
                (if total then "4cm"
                          else "10cm")
             ++ "} || "
             ++ concat (replicate (length proofTypes + if total then 1 else 0)
                                  "c | ")
             ++ "}"
    putStr $ intercalate " & " (" ":
                               (if total then ("total":) else id)
                               (map latexShow proofTypes))
    putStrLn $ " \\\\"

latexCloseTabular :: IO ()
latexCloseTabular = putStrLn "\\end{longtable}"

outputGroup :: Bool -> Name -> String -> Result -> [Res] -> IO ()
outputGroup True  name code status grp = do
    putStrLn "\\hline"
    putStr $ "$" ++ escape name ++ "$"
    putStr " \\newline "
    putStr $ "\\verb`" ++ code ++ "`"
    forM_ proofTypes $ \pt -> do
        let r = minimum (map principleDecor
                             (filter (liberalEq pt .  principleType) grp)
                        ++ [None])
        putStr $ " & " ++ latexResult r
    putStrLn " \\\\ "
outputGroup False name code status grp = do
    putStrLn $ "\n" ++ name
    putStrLn $ code
    putStrLn $ "Status: " ++ show status
    forM_ grp $ \(Principle name ptype res _ parts) -> do
         putStrLn $ "    " ++ show ptype ++ ": " ++ show res
         putStr "        "
         forM_ parts $ \(Part pname pres _) ->
             putStr $ pname ++ ": " ++ show pres ++ " "
         putStrLn ""

outputResGroup :: Bool -> Int -> Result -> ResGroup -> IO ()
outputResGroup True  n res (ResGroup statsMap tot) = do
    putStrLn "\\hline"
    putStr $ latexResult res
    putStr $ " & " ++ show tot ++ "/" ++ show n
    forM_ proofTypes $ \pt -> do
        let m = fromMaybe 0 (M.lookup pt statsMap)
            str = liberalShow pt
        putStr " & "
        when (m > 0) $ putStr $ show m ++ "/" ++ show tot
    putStrLn "\\\\"
outputResGroup False n res (ResGroup statsMap tot) = do
    putStrLn $ show res ++ ":" ++ pad 20 (show res)
            ++ show tot
            ++ "/" ++ show n
    forM_ (M.toList statsMap) $ \(pt,m) -> when (m > 0) $ do
        let str = liberalShow pt
        putStrLn $ "     " ++ str ++ ": " ++ pad 21 str
                 ++ show m ++ "/" ++ show tot


