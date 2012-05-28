{-# LANGUAGE RecordWildCards,ViewPatterns #-}
module Main where

import Hip.Util

import Hip.Trans.MakeTheory
import Hip.Trans.Theory
import Hip.Messages
import Hip.Params

import Hip.Trans.Core

import Hip.Trans.MakeProofs

import Hip.InvokeATPs
import Hip.Trans.ProofDatatypes (propMatter)
import qualified Hip.Trans.ProofDatatypes as PD
import Hip.ResultDatatypes
import Hip.Provers

import Data.List
import Data.Maybe

import Control.Monad
import Control.Applicative
import Control.Arrow ((***),(&&&),second)

import System.Console.CmdArgs hiding (summary)
import System.Exit (exitFailure,exitSuccess)

removeMain :: [CoreBind] > [CoreBind]
removeMain = filter (not . remove)
  where
    remove (NonRec x e) | isMain x = True
    remove _ = False

main :: IO ()
main = do
  params@Params{..} <- cmdArgs defParams

  when (null files) $ do
      putStrLn "No input files. Run with --help to see possible flags"
      exitFailure
  whenLoud $ do putStrLn $ "Verbose output, files: " ++ unwords files
                putStrLn $ "Param: " ++ showParams params

  forM_ files $ \(dropExtension -> file) -> do
      when (file /= head files) $ putStrLn ""
      unless (null files) $ putStrLn $ file ++ ":"
      -- Parse either Haskell or Core

      (modguts,dflags) <- desugar (False {- debug_float_out -}) file

      -- Output debug of translation
      when dbfh (return ())

      -- Output Core and terminate
      when core exitSuccess

      let (core_props,unlifted_program) = filter removeMain
                                        . mg_binds
                                        $ modguts

      us <- mkSplitUniqSupply 'f'
      ((lifted_program,_msgs_lift),_us) <- (`caseLetLift` us) <$> lambdaLift dflags program

      let isPropBinder (NonRec x _) | isPropType x = True
          isPropBinder _ = False

      (core_props,core_defns) = partition isPropBinder lifted_program

      let ty_cons :: [TyCon]
          ty_cons = mg_tcs modguts

          ty_cons_with_builtin :: [TyCon]
          ty_cons_with_builtin = listTyCon : boolTyCon : unitTyCon
                               : map (tupleTyCon BoxedTuple) [2..2]
                                 -- ^ choice: only tuples of size 2 supported!!
                               ++ ty_cons

          cnf = "-cnf" `elem` opts

          halt_conf :: HaltConf
          halt_conf  = sanitizeConf $ HaltConf
                          { use_cnf      = False
                          , inline_projs = True
                          , use_min      = False
                          , common_min   = False
                          , unr_and_bad  = False
                          }

          halt_env = mkEnv halt_conf ty_cons_with_builtin core_defns

          (data_axioms,def_axioms,msgs_trans)
              = translate halt_env ty_cons_with_builtin core_defns

          theory = Theory data_axioms def_axioms (error "Theory.thyTyEnv")

          props' = inconsistentProp : map trProperty props

      (unproved,proved) <- parLoop params theory props' []

      printInfo unproved proved

      return ()

  return ()

printInfo :: [Prop] -> [Prop] -> IO ()
printInfo unproved proved = do
    let pr xs | null xs   = "(none)"
              | otherwise = unwords (map propName xs)
    putStrLn ("Proved: " ++ pr proved)
    putStrLn ("Unproved: " ++ pr unproved)
    putStrLn (show (length proved) ++ "/" ++ show (length (proved ++ unproved)))


-- | Try to prove some properties in a theory, given some lemmas
tryProve :: Params -> [Prop] -> Theory -> [Prop] -> IO [(Prop,Bool)]
tryProve params@(Params{..}) props thy lemmas = do
    let env = Env { reproveTheorems = reprove
                  , timeout         = timeout
                  , store           = output
                  , provers         = proversFromString provers
                  , processes       = processes
                  , propStatuses    = error "main env propStatuses"
                  , propCodes       = error "main env propCodes"
                  }

        (properties,msgs) = second concat
                          . unzip
                          . map (\prop -> theoryToInvocations params thy prop lemmas)
                          $ props

    when dbproof $ mapM_ print (filter (sourceIs MakeProof) msgs)

    when warnings $ mapM_ print (filter isWarning msgs)

    res <- invokeATPs properties env

    forM res $ \property -> do
        let proved = fst (propMatter property) /= None
        when proved (putStrLn $ "Proved " ++ PD.propName property ++ ".")
        return (fromMaybe (error "tryProve: lost")
                          (find ((PD.propName property ==) . propName) props)
               ,proved)

parLoop :: Params -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
parLoop params thy props lemmas = do
    (proved,unproved) <-  (map fst *** map fst) . partition snd
                      <$> tryProve params props thy lemmas
    if null proved then return (props,lemmas)
                   else do putStrLn $ "Adding " ++ show (length proved) ++ " lemmas: " ++ unwords (map propName proved)
                           parLoop params thy unproved (proved ++ lemmas)

