{-# LANGUAGE DeriveDataTypeable, RecordWildCards #-}
module Main where

import qualified Language.TPTP as T
import Language.TPTP.Pretty

import Language.HFOL.FromHaskell.FromHaskell
import Language.HFOL.ToFOL.ToTPTP (toTPTP)
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.ToFOL.ProofDatatypes
import Language.HFOL.ToFOL.Parser
import Language.HFOL.ToFOL.Latex hiding (latex)
import Language.HFOL.Util (putEither)

import System.Console.CmdArgs
import System.Exit (exitFailure,exitSuccess)
import System.IO

import Language.HFOL.RunProver

import Control.Monad
import Control.Applicative
import Data.List (isSuffixOf)
import Data.Either (partitionEithers)

data Params = Params { files     :: [FilePath]
                     , processes :: Int
                     , store     :: Maybe FilePath
                     , timeout   :: Int
                     , latex     :: Bool
                     , tptp      :: Bool
                     , core      :: Bool
                     }
  deriving (Show,Data,Typeable)

params :: Params
params = Params
  { files     = []      &= args &= typFile
  , processes = 4       &= help "Number of prover processes (default 4)"
  , store     = Nothing &= opt (Just "proving/") &= typDir
                        &= help "Store all tptp files in a directory (default proving/)"
  , timeout   = 500     &= help "Timout of provers in milliseconds (default 500)" &= name "t"
  , latex     = False   &= help "Generate latex output and terminate"
  , tptp      = False   &= help "Generate tptp output and terminate" &= name "f"
  , core      = False   &= help "Translate hs to core and terminate"
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
      -- Parse either Haskell or Core
      (eitherds,hsdebug) <- if "hs" `isSuffixOf` file
                                then parseHaskell <$> readFile file
                                else flip (,) []  <$> parseFile file
      ds <- either (\estr -> putStrLn estr >> exitFailure) return eitherds
      -- Output debug of translation
      whenLoud (mapM_ putStrLn hsdebug)
      -- Output Core and terminate
      when core $ do mapM_ (putStrLn . prettyCore) ds
                     exitSuccess
      -- Translation to FOL
      let (funcAxiomsWithDef,extraAxioms,proofs,debug) = toTPTP ds
          axioms = extraAxioms ++ concatMap snd funcAxiomsWithDef
      -- Verbose output
      whenLoud (mapM_ putStrLn debug)
      -- TPTP output
      when tptp $ do putStrLn (prettyTPTP axioms)
                     exitSuccess
      -- Latex output
      when latex $ do
          putStrLn (latexHeader file extraAxioms)
          mapM_ (putStr . uncurry latexDecl) funcAxiomsWithDef
          putStrLn latexFooter
          exitSuccess
      proveAll processes timeout store file axioms proofs

echo :: Show a => IO a -> IO a
echo mx = mx >>= \x -> whenLoud (putStr (show x)) >> return x

untilTrue :: Monad m => (a -> m Bool) -> [a] -> m Bool
untilTrue f (x:xs) = do
  r <- f x
  if r then return True
       else untilTrue f xs
untilTrue _ [] = return False

whileFalse :: Monad m => [a] -> (a -> m Bool) -> m Bool
whileFalse xs p = not `liftM` untilTrue (liftM not . p) xs

proveAll :: Int -> Int -> Maybe FilePath
         -> FilePath -> [T.Decl] -> [ProofDecl] -> IO ()
proveAll processes timeout store file axioms proofs = do
  whenLoud $ do putStrLn $ "Using " ++ show processes ++ " threads."
                putStrLn $ "Timeout is " ++ show timeout
                putStrLn $ "Store directory is " ++ show store
  hSetBuffering stdout NoBuffering
  (fails,ok) <- partitionEithers <$> (forM proofs $ \(ProofDecl name types) -> do
      whenNormal $ putStr $ "Trying to prove " ++ name ++ " "
      r <- untilTrue (prove name) types
      whenNormal $ putStrLn (if r then "\tTheorem!" else "")
      return (putEither r name))
  whenNormal $ putStrLn $ "Succeded : " ++ unwords ok
  whenNormal $ putStrLn $ "Failed : " ++ unwords fails
  putStrLn $ file ++ ": " ++ show (length ok) ++ "/" ++ show (length (ok ++ fails))
  where
    axiomsStr = prettyTPTP axioms
    prove name pt = case pt of
          Induction addBottom indargs parts -> do
              whenLoud $ putStr $ "\n\tby induction on "
                                    ++ (if addBottom then "" else "finite ")
                                    ++ unwords indargs ++ ": \t"
              let probs = map (\(IndPart indcons decls) ->
                                     (concat indcons
                                     ,file ++ name ++ concat indargs
                                           ++ concat indcons ++ ".tptp"
                                     ,axiomsStr ++ prettyTPTP decls)) parts
              all ((== Theorem) . snd) <$>
                  echo (runProvers processes timeout store probs)
          ApproxLemma decls -> do
              whenLoud $ putStr $ "\n\tby approximation lemma "
              let prob = ("approx",file ++ name ++ "approx.tptp"
                         ,axiomsStr ++ prettyTPTP decls)
              all ((== Theorem) . snd) <$>
                  echo (runProvers processes timeout store [prob])
          _ -> return False
{-
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
-}
{-          Plain decls -> do
              putStr "\tby definition.."
              let fname = "prove/" ++ file ++ name ++ "plain.tptp"
              writeFile fname (axiomsStr ++ prettyTPTP decls)
              r <- echo (runProver fname)
              if r == Theorem
                  then putStrLn "\tTheorem!" >> return True
                  else putStrLn "" >> return False
-}

