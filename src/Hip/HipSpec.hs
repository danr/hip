{-# LANGUAGE RecordWildCards #-}
module Hip.HipSpec (hipSpec, module Test.QuickSpec.Term) where

import Test.QuickSpec.Term
import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Equations

import Hip.Util
import Hip.Trans.MakeTheory
import Hip.Trans.Theory
import Hip.Messages
import Hip.Params
import Hip.Trans.Parser
import Hip.Trans.Core as C
import Hip.Trans.Pretty
import Hip.FromHaskell.FromHaskell
import Hip.Trans.MakeProofs
import Hip.InvokeATPs
import Hip.Trans.ProofDatatypes (propMatter)
import qualified Hip.Trans.ProofDatatypes as PD
import Hip.ResultDatatypes
import Hip.Provers

import Language.TPTP.Pretty

import Data.List
import Data.Maybe
import Data.Typeable
import Data.Char

import Control.Monad
import Control.Applicative
import Control.Arrow ((***),(&&&),second)

import System.IO
import System.Console.CmdArgs hiding (summary,name)
import System.Exit (exitFailure,exitSuccess)


termToExpr :: Term Symbol -> Expr
termToExpr t = case t of
  T.App e1 e2 -> termToExpr e1 `app` termToExpr e2
  T.Var s     -> C.Var (name s)
  T.Const s | isUpper . head . name $ s -> Con (name s) []
            | otherwise                 -> C.Var (name s)

-- So far only works on arguments with monomorphic, non-exponential types
termsToProp :: Term Symbol -> Term Symbol -> Prop
termsToProp lhs rhs = Prop { proplhs  = termToExpr lhs
                           , proprhs  = termToExpr rhs
                           , propVars = map (name . fst) typedArgs
                           , propName = repr
                           , propType = TyApp (map snd typedArgs ++ [error $ "res on qs prop " ++ repr])
                           , propRepr = repr ++ " (from quickSpec)"
                           }
  where
    typedArgs = map (id &&& typeableType . symbTypeRep) (vars lhs ++ vars rhs)
    repr = show lhs ++ " = " ++ show rhs

typeableType :: TypeRep -> Type
typeableType tr
  | tyConString (typeRepTyCon tr) == "Int" = TyVar "a"
  | otherwise = TyCon (fixTyConString . tyConString . typeRepTyCon $ tr)
                        (map typeableType (typeRepArgs tr))
     where
       fixTyConString = reverse . takeWhile (/= '.') . reverse


hipSpec :: FilePath -> [Symbol] -> Int -> IO ()
hipSpec file conf depth = do
  hSetBuffering stdin LineBuffering

  params@Params{..} <- cmdArgs (hipSpecParams file)

  (eitherds,hsdebug) <- if "hs" `isSuffixOf` file
                            then parseHaskell <$> readFile file
                            else flip (,) []  <$> parseFile file
  (err,ds) <- case eitherds of
                    Left  estr -> putStrLn estr >> return (True,error estr)
                    Right ds'  -> return (False,ds')
  unless err $ do
    -- Output debug of translation
    when dbfh $ do
      putStrLn "Translating from Haskell..."
      mapM_ print (filter (sourceIs FromHaskell) hsdebug)
      putStrLn "Translation from Haskell translation complete."
    -- Output warnings of translation
    when warnings $ mapM_ print (filter isWarning hsdebug)
    -- Output Core and terminate
    when core $ do mapM_ (putStrLn . prettyCore) ds
                   exitSuccess

    let (theory,props,msgs) = makeTheory params ds

     -- Verbose output
    when dbfol $ mapM_ print (filter (sourceIs Trans) msgs)

    -- Warnings
    when warnings $ mapM_ print (filter isWarning msgs)

    let props' | consistency = inconsistentProp : props
               | otherwise   = props

    putStrLn "Translation complete. Generating equivalence classes."

    -- eqclasses :: [(Term Symbol,Term Symbol)]
    eqclasses <- packLaws depth conf True (const True) (const True)

    putStrLn "Starting to prove..."

    let quickSpecProps = map (uncurry termsToProp) eqclasses

    (unproved,proved) <- parLoop params theory (quickSpecProps ++ props') []

    printInfo unproved proved

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

proveLoop :: Params -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
proveLoop params thy props lemmas = do
   new <- forFind (inspect props) $ \(p,ps) -> snd . head <$> tryProve params [p] thy lemmas
   case new of
     -- Property p was proved and ps are still left to prove
     Just (p,ps) -> do putStrLn ("Proved " ++ propName p ++ ": " ++ propRepr p ++ ".")
                       proveLoop params thy ps (p:lemmas)
     -- No property was proved, return the unproved properties and the proved ones
     Nothing     -> return (props,lemmas)

parLoop :: Params -> Theory -> [Prop] -> [Prop] -> IO ([Prop],[Prop])
parLoop params thy props lemmas = do
    (proved,unproved) <-  (map fst *** map fst) . partition snd
                      <$> tryProve params props thy lemmas
    if null proved then return (props,lemmas)
                   else do putStrLn $ "Adding " ++ show (length proved) ++ " lemmas: " ++ unwords (map propName proved)
                           parLoop params thy unproved (proved ++ lemmas)


