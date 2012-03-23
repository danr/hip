{-# LANGUAGE RecordWildCards #-}
module Hip.HipSpec (hipSpec, module Test.QuickSpec.Term) where

import Test.QuickSpec.Term
import qualified Test.QuickSpec.Term as T
import Test.QuickSpec.Equations
import Test.QuickSpec.CongruenceClosure

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
import Data.Ord

import Control.Monad
import Control.Applicative
import Control.Arrow ((***),(&&&),second)

import System.IO
import System.Console.CmdArgs hiding (summary,name)
import System.Exit (exitFailure,exitSuccess)

type QSEq = (Term Symbol,Term Symbol)

deep :: Params -> Theory -> [Symbol] -> Int -> [Term Symbol] -> [QSEq] -> IO ([Prop],[QSEq])
deep params theory ctxt depth univ eqs = loop (initPrune ctxt univ) eqs [] [] False
  where
    loop :: PruneState -> [QSEq] -> [QSEq] -> [Prop] -> Bool -> IO ([Prop],[QSEq])
    loop ps@(_,cc) [] failed proved True  = putStrLn "Loop!" >> loop ps failed [] proved False
    loop ps@(_,cc) [] failed proved False = return (proved,failed)
    loop ps@(_,cc) (eq@(lhs,rhs):eqs) failed proved retry
      | evalCC cc (canDerive lhs rhs) = do

           putStrLn $ "No need to prove " ++ show lhs ++ " = " ++ show rhs ++ ", skipping."
           loop ps eqs failed proved retry

      | otherwise = do

           [(prop,success)] <- tryProve params [termsToProp lhs rhs] theory proved
           if success then let (cand,failed') = instancesOf ps eq failed
                               (_,ps') = doPrune (const True) ctxt depth [eq] [] ps
                           in do putStrLn $ "Interesting candidates: " ++
                                            intercalate ", " (map (\(u,v) -> show u ++ " = " ++ show v) cand)
                                 loop ps' (cand ++ eqs) failed' (prop:proved) True
                      else loop ps eqs (failed ++ [eq]) proved retry

    instancesOf :: PruneState -> QSEq -> [QSEq] -> ([QSEq],[QSEq])
    instancesOf ps new = partition (instanceOf ps new)

    instanceOf :: PruneState -> QSEq -> QSEq -> Bool
    instanceOf ps new cand =
       let (_,(_,cc)) = doPrune (const True) ctxt depth [cand] [] ps
       in  evalCC cc (uncurry canDerive new)

  {-
    loop :: PruneState -> [QSEq] -> [Prop] -> IO ([Prop],[QSEq])
    loop ps@(_,cc) eqs proved = do
      let (skip,eqs') = partition (\(lhs,rhs) -> evalCC cc (canDerive lhs rhs)) eqs
      forM_ skip $ \(lhs,rhs) -> putStrLn $ "No need to prove " ++ show lhs ++ " = "
                                                                ++ show rhs ++ ", skipping."
      res <- tryProve params (map (uncurry termsToProp) eqs') theory proved
      let (successes,failures) = (map fst *** map fst) (partition snd res)
          (_,ps') = doPrune (const True) ctxt depth (map propQSTerms successes) [] ps
          failureQSEqs = map propQSTerms failures
      if null successes
          then return (proved,failureQSEqs)
          else loop ps' (map propQSTerms failures) (successes ++ proved)

          -}

{-
-}

termToExpr :: Term Symbol -> Expr
termToExpr t = case t of
  T.App e1 e2 -> termToExpr e1 `app` termToExpr e2
  T.Var s     -> C.Var (name s)
  T.Const s | (isUpper . head . name $ s) || name s == ":"
                                          || name s == "[]" -> Con (name s) []
            | otherwise                                     -> C.Var (name s)

-- So far only works on arguments with monomorphic, non-exponential types
termsToProp :: Term Symbol -> Term Symbol -> Prop
termsToProp lhs rhs = Prop { proplhs  = termToExpr lhs
                           , proprhs  = termToExpr rhs
                           , propVars = map (name . fst) typedArgs
                           , propName = repr
                           , propType = TyApp (map snd typedArgs ++ [error $ "res on qs prop " ++ repr])
                           , propRepr = repr ++ " (from quickSpec)"
                           , propQSTerms = (lhs,rhs)
                           }
  where
    typedArgs = map (id &&& typeableType . symbTypeRep) (nub (vars lhs ++ vars rhs))
    repr = show lhs ++ " = " ++ show rhs

typeableType :: TypeRep -> Type
typeableType tr
  | tyConName (typeRepTyCon tr) == "Int" = TyVar "a"
  | otherwise = TyCon (tyConName . typeRepTyCon $ tr)
                        (map typeableType (typeRepArgs tr))
     -- where
     --   fixTyConString = reverse . takeWhile (/= '.') . reverse


hipSpec :: FilePath -> [Symbol] -> Int -> IO ()
hipSpec file ctxt depth = do
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

    let classToEqs :: [[Term Symbol]] -> [(Term Symbol,Term Symbol)]
        classToEqs = sortBy (comparing equationOrder)
                   . concatMap ((\(x:xs) -> zip (repeat x) xs) . sort)

    quickSpecClasses <- packLaws depth ctxt True (const True) (const True)

    putStrLn "Equivalence classes:"
    forM_ quickSpecClasses $ \cl -> putStrLn $ intercalate " = " (map show cl)

    putStrLn "With representatives:"
    putStrLn $ unlines (map (\(l,r) -> show l ++ " = " ++ show r)
                            (classToEqs quickSpecClasses))

    let univ = concat quickSpecClasses

    putStrLn "Starting to prove..."

    (qslemmas,qsunproved) <- deep params theory ctxt depth univ (classToEqs quickSpecClasses)

    (unproved,proved) <- parLoop params theory props' qslemmas

    printInfo unproved proved

    return ()

printInfo :: [Prop] -> [Prop] -> IO ()
printInfo unproved proved = do
    let pr xs | null xs   = "(none)"
              | otherwise = intercalate ",\n\t" (map propName xs)
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
        when   proved (putStrLn $ "Proved " ++ PD.propName property ++ ".")
        unless proved (putStrLn $ "Failed to prove " ++ PD.propName property ++ ".")
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
                   else do putStrLn $ "Adding " ++ show (length proved) ++ " lemmas: " ++ intercalate ", " (map propName proved)
                           parLoop params thy unproved (proved ++ lemmas)


