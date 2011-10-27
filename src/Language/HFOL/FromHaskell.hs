{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleContexts #-}
module Language.HFOL.FromHaskell where

import qualified Language.Haskell.Exts as H
import Language.Haskell.Exts hiding (Name)

import qualified Language.HFOL.Core as C
import Language.HFOL.Core hiding (Decl)

import Language.HFOL.Pretty

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.RWS

import Data.List (groupBy)
import Data.Function (on)
import Data.Either (partitionEithers)

newtype FH a = FH (ErrorT String (RWS Env [Either String C.Decl] St) a)
  deriving(Functor,Applicative,Monad
          ,MonadWriter [Either String C.Decl]
          ,MonadReader Env
          ,MonadState St)

type St = ()

type Env = ()

initSt :: St
initSt = ()

initEnv :: Env
initEnv = ()

write :: String -> FH ()
write = tell . return . Left

warn :: String -> FH ()
warn = write . ("Warning: " ++)

runFH :: FH () -> (Either String [C.Decl],[String])
runFH (FH m) = case evalRWS (runErrorT m) initEnv initSt of
  (Left err,w) -> (Left err,fst (partitionEithers w))
  (Right (),w) -> let (msgs,decls) = partitionEithers w
                  in  (Right decls,msgs)

decl :: C.Decl -> FH ()
decl = tell . return . Right

run :: FilePath -> IO ()
run f = do
  r <- parseFile f
  case r of
    ParseOk m ->
      case runFH (fromModule m) of
        (Left err,msgs) -> do
          mapM_ putStrLn msgs
          putStrLn ""
          putStrLn err
        (Right ds,msgs) -> do
          mapM_ putStrLn msgs
          putStrLn ""
          mapM_ (putStrLn . prettyCore) ds
    ParseFailed loc s -> putStrLn $ show loc ++ ": " ++ s

indented :: String -> String
indented = unlines . map ("    " ++) . lines

fromModule :: Module -> FH ()
fromModule (Module loc name pragmas warnings exports imports decls) =
  mapM_ fromDecl decls

fromDecl :: Decl -> FH ()
fromDecl d = case d of
  DataDecl loc dataornew ctxt name tyvars qualcondecls derives ->
    (decl . Data) =<< mapM fromQualConDecl qualcondecls
--  FunBind matches -> fromMatches matches
  e -> do
    warn $ "Nothing produced for declaration: \n" ++ indented (prettyPrint e)
    write $ indented (show e)


fromQualConDecl :: QualConDecl -> FH (Name,Int)
fromQualConDecl (QualConDecl loc tyvars cxtx condecl) = fromConDecl condecl

fromName :: H.Name -> Name
fromName (Ident s)  = s
fromName (Symbol s) = s

fromQName :: QName -> FH Name
fromQName q@(Qual modulename name) = do
  warn $ "No handling for qualifed names: " ++ prettyPrint q
  return (fromName name)
fromQName (UnQual name) = return (fromName name)
fromQName (Special special) = fromSpecial special

fromSpecial :: SpecialCon -> FH Name
fromSpecial UnitCon = return "()"
fromSpecial ListCon = return "[]"
fromSpecial FunCon  = warn "Using FunCon" >> return "->"
fromSpecial (TupleCon b n) = do
  when (b == Boxed) $ warn "No handling of boxed tuples"
  return ("T" ++ show n)
fromSpecial Cons    = return ":"
fromSpecial UnboxedSingleCon = do
  warn "No handling of unboxed singleton constructor"
  return "()"

fromConDecl :: ConDecl -> FH (Name,Int)
fromConDecl c = case c of
  ConDecl name bangtypes                  -> return (fromName name,length bangtypes)
  InfixConDecl _bangtype1 name _bangtype2 -> return (fromName name,2)
  RecDecl name namedbangtypes             -> do
      warn $ "not creating projection declarations (" ++ fromName name ++ ")"
      return (fromName name,length namedbangtypes)

matchName :: Match -> H.Name
matchName (Match _ name _ _ _ _) = name

fromMatches :: [Match] -> FH ()
fromMatches = mapM_ fromFunMatches . groupBy ((==) `on` matchName)

concatMapM f xs = concat <$> mapM f xs

fromFunMatches :: [Match] -> FH ()
fromFunMatches ms = decl =<< funcMatrix (fromName (matchName (head ms)))
                 <$> (concatMapM matchToRow ms)

matchToRow :: Match -> FH [([Pattern],Maybe C.Expr,C.Expr)]
matchToRow (Match loc name ps mtype rhs binds) = do
  when undefined $ -- (not (null binds)) $
    warn $ "Not generating any binds for where clause" ++ show binds
  return []
{-  case rhs of
    UnGuardedRhs e ->
    GuardedRhs guards
-}

fromPat :: Pat -> FH Pattern
fromPat pat = case pat of
  H.PVar name   -> return (C.PVar (fromName name))
  PTuple ps     -> PCon ("T" ++ show (length ps)) <$> mapM fromPat ps
  PParen p      -> fromPat p
  PWildCard     -> return PWild
  PatTypeSig loc p ty -> do
    warn $ "Ignored type signature in pattern " ++ prettyPrint pat
    fromPat p
  PAsPat name p -> do
    warn $ "No handling of as patterns: " ++ prettyPrint pat
    fromPat p
  PInfixApp p1 qname p2 ->
    (\n a b -> PCon n [a,b]) <$> fromQName qname <*> fromPat p1 <*> fromPat p2
  _ -> do
    warn $ "No handling for pattern: " ++ prettyPrint pat
    warn "Defaulting to PWild!"
    return PWild

