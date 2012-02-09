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

import System.Console.CmdArgs hiding (summary)
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
  whenLoud $ do putStrLn $ "Verbose output, files: " ++ unwords files
                putStrLn $ "Param: " ++ showParams params
  when (latex && not tptp) $ latexHeader'

  totalRes <- forM files $ \file -> (,) file <$> do
      when (file /= head files) $ putStrLn ""
      when (length files > 1) $ outputSection latex file
      -- Parse either Haskell or Core
      (eitherds,hsdebug) <- if "hs" `isSuffixOf` file
                                then parseHaskell <$> readFile file
                                else flip (,) []  <$> parseFile file
      (err,ds) <- case eitherds of
                        Left  estr -> putStrLn estr >> return (True,error estr)
                        Right ds'   -> return (False,ds')
      if err then return [] else do
        -- Output debug of translation
        when dbfh $ do
          putStrLn "Translating from Haskell..."
          mapM_ print (filter (sourceIs FromHaskell) hsdebug)
          putStrLn "Translation from Haskell translation complete."
        -- Output warnings of translation
        when (warnings && not latex) $ mapM_ print (filter isWarning hsdebug)
        -- Output Core and terminate
        when core $ do mapM_ (putStrLn . prettyCore) ds
                       exitSuccess
        -- Don't prove anything, just dump translations
        if tptp || consistency then do
            -- Translation to FOL
            let (funcAxiomsWithDef,extraAxioms,debug) = dumpTPTP params ds
                axioms = extraAxioms ++ concatMap snd funcAxiomsWithDef
            -- Verbose output
            when dbfol $ mapM_ print (filter (sourceIs ToFOL) debug)
            -- Warnings
            when (warnings && not latex) $ mapM_ print (filter isWarning debug)
            -- TPTP output
            if consistency
              then proveAll latex processes timeout output reprove (proversFromString provers) file
                            [Property "consistency" "" [Part Plain Infinite
                                                             (axioms,[Particle "consistency" []])]]
              else if latex
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
            when (warnings && not latex) $ mapM_ print (filter isWarning debug)
            whenLoud $ putStrLn "Done preparing proofs"
            proveAll latex processes timeout output reprove (proversFromString provers) file proofs

  let propRes :: [PropResult]
      propRes = concatMap snd totalRes

  when (length files > 1 || statistics) $ do

    putStrLn "-- Total summary --------------------------------------------------"
    putStrLn $ stringSummary propRes

    when statistics $ do
         let header = "% " ++ showParams params
         writeFile "statistics.data" $ unlines $
              [header,tableHeader] ++
              map (uncurry tableSummary) totalRes ++
              [tableSummary "Total" propRes | length files > 1 ]
         forM_ (times propRes) $ \(st,mm,ts) -> do
              let fname = show st ++ "_" ++ maybe "" liberalShow mm ++ "Times.data"
              writeFile fname (header ++ "\n" ++ unwords (map show ts) ++ "\n")

echo :: Show a => IO a -> IO a
echo mx = mx >>= \x -> whenLoud (putStr (show x)) >> return x


proveAll :: Bool -> Int -> Int -> Maybe FilePath -> Bool -> [Prover]
         -> FilePath -> [Property]
         -> IO [PropResult]
proveAll latex processes timeout output reprove provers file properties = do
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
         forM_ parts $ \part@(Part partMethod partCoverage particles) ->
              when (statusFromPart part > None) $ do
                  putStrLn $ "  " ++ show partMethod ++ ": " ++ show (statusFromPart part) ++
                             " (" ++ intercalate ", " (map (\(Particle _ (result,_)) -> show (successTime result `div` 1000) ++ "ms") particles) ++ ")"
         putStrLn ""

    putStrLn $ stringSummary propRes

    return propRes

pad :: Int -> String -> String
pad x s   = s ++ replicate (x - length s) ' '

latexCloseTabular :: IO ()
latexCloseTabular = putStrLn "\\end{longtable}"

data MethSum = MethSum { method    :: ProofMethod
                       , quantity  :: Int          -- of theorems proved with this
                       , average   :: Double       -- of all ways proved with this
                       , maxima    :: Integer      -- dito
                       }

stringSummary :: [PropResult] -> {- [(Status,[MethSum])] -> -} String
stringSummary res = unlines
                  $ concatMap (\(st,i,ms) -> [show st ++ " " ++ show i ++ "/" ++ show n ++ ":"] ++
                                             map (("    "++) . methSummary i) ms)
                  $ summary res
  where
    n = length res
    methSummary :: Int -> MethSum -> String
    methSummary i (MethSum{..}) = pad 23 (liberalShow method ++ ":") ++ " " ++ pad 7 (show quantity ++ "/" ++ show i ++ ",") ++
                                  "avg:" ++ pad 8 (takeWhile (/= '.') (show average) ++ "ms,") ++
                                  "max:" ++ show maxima ++ "ms"

tableMethods :: [(Status,[ProofMethod])]
tableMethods = [(Theorem,[Plain
                          ,StructuralInduction [] True 0
                          ,ApproxLemma
                          ,FixpointInduction []
                          ])
               ,(FiniteTheorem,[StructuralInduction [] False 0])
               ]

tableHeader :: String
tableHeader = intercalate " & " ("" : concatMap flat tableMethods)
  where flat (st,ms) = show st:map liberalShow ms

tableSummary :: FilePath -> [PropResult] -> String
tableSummary file res = intercalate " & " (file:process Theorem ++ process FiniteTheorem)
   where
     sum :: [(Status,Int,[MethSum])]
     sum = summary res

     n = length res

     fst3 (a,_,_) = a

     process :: Status -> [String]
     process status = case find ((status ==) . fst3) sum of
                        Just (_,i,methsums) -> (show i ++ "/" ++ show n):map (methSummary i methsums) meths
                        Nothing             -> "":map (const "") meths
       where
         meths :: [ProofMethod]
         meths = fromMaybe (error "tableSummary: meths") (lookup status tableMethods)

         methSummary :: Int -> [MethSum] -> ProofMethod -> String
         methSummary i methsums m = case find ((m `liberalEq`) . method) methsums of
                                      Just (MethSum{..}) -> show quantity ++ "/" ++ show i
                                      Nothing            -> ""

times :: [PropResult] -> [(Status,Maybe ProofMethod,[Integer])]
times res = filter (not . null . trd) (process Theorem ++ process FiniteTheorem)
  where
    trd (_,_,c) = c

    process status = (status,Nothing,criteria status (const True)):
                     map (\m -> (status,Just m,criteria status (liberalEq m)))
                         (fromMaybe (error "times") (lookup status tableMethods))

    criteria :: Status -> (ProofMethod -> Bool) -> [Integer]
    criteria status p = concatMap handlePart
                      $ concatMap (snd . propMatter)             -- get these parts
                      $ filter ((status ==) . fst . propMatter)  -- only with this status
                      $ res
      where
        handlePart :: PartResult -> [Integer]
        handlePart part = case p (partMethod part) && statusFromPart part == status of
           True  -> map (successTime . fst . particleMatter) (partMatter part)
           False -> []


summary :: [PropResult] -> [(Status,Int,[MethSum])]
summary = map (\xs@((status,_):_) ->
                  (status
                  ,length (filter ((status ==) . fst) xs)
                  ,sumParts  status (map snd xs)))
        . reverse                           -- thm,fin
        . groupSortedOn fst                 -- [[(Status,[PartResult])]]
        . filter ((None /=) . fst)          -- remove none
        . map propMatter                    -- [(Status,[PartResult])]


sumParts :: Status -> [[PartResult]] -> [MethSum]
sumParts status pparts = mapMaybe handleMethod proofMethods
  where
    handleMethod :: ProofMethod -> Maybe MethSum
    handleMethod method = res
      where
         partProvedByMethod :: PartResult -> Bool
         partProvedByMethod part = method `liberalEq` partMethod part
                                && statusFromPart part == status

         qty = length (filter (any partProvedByMethod) pparts)

         fi = fromIntegral
         itod = fi . toInteger

         makeMethSum :: [ProverResult] -> Int -> MethSum
         makeMethSum ss nums = MethSum
                                  { method   = method
                                  , quantity = qty
                                  , average  = fi (sum (map successTime ss)) / itod nums / 1000
                                  , maxima   = maximum (map successTime ss) `div` 1000
                                  }

         res | qty == 0  = Nothing
             | otherwise = Just
                         $ (makeMethSum <*> length)
                         $ concatMap (map (fst . particleMatter) . partMatter)
                         $ filter partProvedByMethod
                         $ concat pparts

