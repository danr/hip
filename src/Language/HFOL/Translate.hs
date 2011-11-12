module Main where

import qualified Language.TPTP as T
import Language.TPTP.Pretty

import Language.HFOL.FromHaskell.FromHaskell
import Language.HFOL.ToFOL.ToTPTP (toTPTP)
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.ToFOL.ProofDatatypes
import Language.HFOL.ToFOL.Parser
import Language.HFOL.ToFOL.Latex

import System.Environment (getArgs)
import System.Exit (exitFailure,exitSuccess)
import System.Process (readProcessWithExitCode)
import System.IO

import Control.Monad (when,forM_,forM)
import Control.Applicative ((<$>))
import Data.List (isSuffixOf,isInfixOf)
import Data.Either (partitionEithers)

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
      -- Proof mode
      let proofMode = flag "-p"
      -- Translation to FOL
      let (funcAxiomsWithDef,extraAxioms,proofs,debug) = toTPTP proofMode ds
          axioms = extraAxioms ++ concatMap snd funcAxiomsWithDef
      -- Verbose output
      when (flag "-v") (mapM_ putStrLn debug)
      -- TPTP output
      when (flag "-t" || not (flag "-l") && not proofMode) (putStrLn (prettyTPTP axioms))
      -- Latex output
      when (flag "-l") $ do
          putStrLn (latexHeader file extraAxioms)
          mapM_ (putStr . uncurry latexDecl) funcAxiomsWithDef
          putStrLn latexFooter
      when proofMode $ proveAll file axioms proofs

data ProverResult = Timeout
                  | Theorem
                  | Falsifiable
  deriving (Eq,Ord)

instance Show ProverResult where
  show Timeout     = "timeout"
  show Theorem     = "ok"
  show Falsifiable = "false"

runProver :: FilePath -> IO ProverResult
runProver f = do
    (_exitcode,stdout,_stderr) <-
      readProcessWithExitCode
        "timeout"
        (words "1 eprover -tAuto -xAuto --memory-limit=1000 --tptp3-format -s"
                ++ [f])
        ""
    case () of () | "Theorem" `isInfixOf` stdout            -> return Theorem
                  | "CounterSatisfiable" `isInfixOf` stdout -> return Falsifiable
                  | otherwise                               -> return Timeout

echo :: Show a => IO a -> IO a
echo mx = mx >>= \x -> putStr (show x) >> return x

untilTrue :: Monad m => (a -> m Bool) -> [a] -> m Bool
untilTrue f (x:xs) = do
  r <- f x
  if r then return True
       else untilTrue f xs
untilTrue _ [] = return False

putEither :: Bool -> a -> Either a a
putEither True  = Right
putEither False = Left

proveAll :: FilePath -> [T.Decl] -> [ProofDecl] -> IO ()
proveAll file axioms proofs = do
  hSetBuffering stdout NoBuffering
  (fails,ok) <- partitionEithers <$> (forM proofs $ \(ProofDecl name types) -> do
      putStrLn $ "Trying to prove " ++ name
      (`putEither` name) <$> untilTrue (prove name) types)
  putStrLn $ "Succeded : " ++ unwords ok
  putStrLn $ "Failed : " ++ unwords fails
  where
    axiomsStr = prettyTPTP axioms
    prove name pt = case pt of
          Induction vars base step -> do
              putStr $ "\tinduction on " ++ unwords vars ++ ":  \t"
              let fbase = "prove/" ++ file ++ name ++ concat vars ++ "base.tptp"
              writeFile fbase (axiomsStr ++ prettyTPTP base)
              let fstep = "prove/" ++ file ++ name ++ concat vars ++ "step.tptp"
              writeFile fstep (axiomsStr ++ prettyTPTP step)
              putStr "base..."
              b <- echo (runProver fbase)
              putStr " step..."
              s <- echo (runProver fstep)
              if b == Theorem && s == Theorem
                  then putStrLn "\tTheorem!" >> return True
                  else putStrLn "" >> return False
          Plain ts -> do
              putStr "\tby definition... "
              let fname = "prove/" ++ file ++ name ++ "plain.tptp"
              writeFile fname (axiomsStr ++ prettyTPTP ts)
              r <- echo (runProver fname)
              if r == Theorem
                  then putStrLn "\tTheorem!" >> return True
                  else putStrLn "" >> return False

printUsage :: IO ()
printUsage = mapM_ putStrLn
  [ "Usage:"
  , "    autospec filename [flags]"
  , ""
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



