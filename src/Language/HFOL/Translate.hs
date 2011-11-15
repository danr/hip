module Main where

import qualified Language.TPTP as T
import Language.TPTP.Pretty

import Language.HFOL.FromHaskell.FromHaskell
import Language.HFOL.ToFOL.ToTPTP (toTPTP)
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.ToFOL.ProofDatatypes
import Language.HFOL.ToFOL.Parser
import Language.HFOL.ToFOL.Latex
import Language.HFOL.Util (putEither)

import System.Environment (getArgs)
import System.Exit (exitFailure,exitSuccess)
import System.Process (readProcessWithExitCode)
import System.IO

import Control.Monad (when,forM_,forM,liftM)
import Control.Applicative ((<$>),(<*>))
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
    (_exitcode,out,_err) <-
      readProcessWithExitCode
        "timeout"
        (words "1 eprover -tAuto -xAuto --memory-limit=1000 --tptp3-format -s"
                ++ [f])
        ""
--    putStrLn out
    case () of () | "Theorem" `isInfixOf` out            -> return Theorem
                  | "Unsatisfiable" `isInfixOf` out      -> return Theorem
                  | "CounterSatisfiable" `isInfixOf` out -> return Falsifiable
                  | otherwise                            -> return Timeout

echo :: Show a => IO a -> IO a
echo mx = mx >>= \x -> putStr (show x) >> return x

untilTrue :: Monad m => (a -> m Bool) -> [a] -> m Bool
untilTrue f (x:xs) = do
  r <- f x
  if r then return True
       else untilTrue f xs
untilTrue _ [] = return False

whileFalse :: Monad m => [a] -> (a -> m Bool) -> m Bool
whileFalse xs p = not `liftM` untilTrue (liftM not . p) xs

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
          NegInduction indargs decls -> do
              putStr $ "\tnegated induction on " ++ unwords indargs ++ ": \t"
              let fname = "prove/" ++ file ++ name ++ concat indargs ++ "negind.tptp"
              writeFile fname (axiomsStr ++ prettyTPTP decls)
--              mapM_ (putStrLn . prettyTPTP) decls
              putStr "\t"
              r <- echo (runProver fname)
              if r == Theorem
                  then putStrLn "\tTheorem!" >> return True
                  else putStrLn "" >> return False
          Induction addBottom indargs parts -> do
              putStr $ "\tinduction on " ++ (if addBottom then "" else "finite ") ++ unwords indargs ++ ": \t"
              r <- whileFalse parts $ \(IndPart indcons decls) -> do
                  let fname = "prove/" ++ file ++ name ++ concat indargs ++ concat indcons ++ ".tptp"
                  writeFile fname (axiomsStr ++ prettyTPTP decls)
                  putStr $ " " ++ unwords indcons ++ ".."
                  r <- echo (runProver fname)
                  return (r == Theorem)
              if r
                  then putStrLn "\tTheorem!" >> return True
                  else putStrLn "" >> return False
          Plain decls -> do
              putStr "\tby definition.."
              let fname = "prove/" ++ file ++ name ++ "plain.tptp"
              writeFile fname (axiomsStr ++ prettyTPTP decls)
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



