{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleContexts,TemplateHaskell #-}
module Language.HFOL.FromHaskell where

import qualified Language.Haskell.Exts as H
import Language.Haskell.Exts hiding (Name,app)

import qualified Language.HFOL.Core as C
import Language.HFOL.Core hiding (Decl)

import Language.HFOL.Pretty

import Data.Label (mkLabels)
import Data.Label.PureM

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.RWS hiding (gets,modify)

import Data.List (groupBy)
import Data.Function (on)
import Data.Either (partitionEithers)

data St = St { _namesupply :: [Int] }
$(mkLabels [''St])

data Env = Env { _scope :: String }
$(mkLabels [''Env])

initSt :: St
initSt = St { _namesupply = [0..] }

initEnv :: Env
initEnv = Env { _scope = "" }

newtype FH a = FH (ErrorT String (RWS Env [Either String C.Decl] St) a)
  deriving(Functor,Applicative,Monad
          ,MonadWriter [Either String C.Decl]
          ,MonadReader Env
          ,MonadState St
          ,MonadError String)

write :: String -> FH ()
write = tell . return . Left

warn :: String -> FH ()
warn = write . ("Warning: " ++)

fatal :: String -> FH a
fatal = throwError

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
  FunBind matches -> fromMatches matches
  PatBind{}       -> fromPatBind d
  e -> do
    warn $ "Nothing produced for declaration: \n" ++ indented (prettyPrint e)
    write $ indented (show e)

fromMatches :: [Match] -> FH ()
fromMatches = mapM_ fromFunMatches . groupBy ((==) `on` matchName)

concatMapM :: (Functor m,Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> mapM f xs

fromFunMatches :: [Match] -> FH ()
fromFunMatches [] = warn $ "Empty funmatches"
fromFunMatches ms@(m:_) = do
   matrix <- concatMapM matchToRow ms
   if null matrix
       then warn $ "Empty matrix from " ++ show (matchName m)
       else decl (funcMatrix (fromName (matchName m)) matrix)

fromPatBind :: Decl -> FH ()
fromPatBind (PatBind loc (H.PVar name) mtype rhs binds) =
  fromFunMatches [Match loc name [] mtype rhs binds]
fromPatBind pb@(PatBind loc p mtype rhs binds) =
  fatal $ "Top level patterns not supported : " ++ prettyPrint pb
fromPatBind d = fatal $ "Internal error, fromPatBind on decl " ++ show d

matchToRow :: Match -> FH [([Pattern],Maybe C.Expr,Expr)]
matchToRow (Match loc name ps mtype rhs binds) = do
  fromBinds binds
  return []
  case rhs of
    UnGuardedRhs e     -> do ps' <- mapM fromPat ps
                             e' <- fromExp e
                             return [(ps',Nothing,e')]
    GuardedRhss guards -> do warn $ "no handling of guards" ++ prettyPrint rhs
                             return []

----------------------------------------------------------------------
-- Expressions

fromExp :: Exp -> FH Expr
fromExp e = case e of
  H.Var qn           -> C.Var <$> fromQName qn
  H.Con qn           -> con0  <$> fromQName qn
  H.App e1 e2        -> C.app <$> fromExp e1 <*> fromExp e2
  Paren e            -> fromExp e
  InfixApp e1 qop e2 -> (app .) . app <$> fromQOp qop <*> fromExp e1 <*> fromExp e2
  Lambda loc ps e    -> fatal "No lambda"
  H.Case e alts      -> fatal "No case exps"
  Let binds e        -> fatal "No lets"
  Tuple es           -> C.Con ('T':show (length es)) <$> mapM fromExp es
  If e1 e2 e3        -> (app .) . app . (app (C.Var "if")) <$> fromExp e1
                                                           <*> fromExp e2
                                                           <*> fromExp e3
  _ -> fatal $ "No handling of expression " ++ prettyPrint e ++ "\n\n" ++ show e


fromQOp :: QOp -> FH Expr
fromQOp (QVarOp qname) = C.Var <$> fromQName qname
fromQOp (QConOp qname) = con0  <$> fromQName qname

----------------------------------------------------------------------
-- Patterns

fromPat :: Pat -> FH Pattern
fromPat pat = case pat of
  H.PVar name   -> return (C.PVar (fromName name))
  PTuple ps     -> PCon ('T':show (length ps)) <$> mapM fromPat ps
  PParen p      -> fromPat p
  PWildCard     -> return PWild
  PApp qname ps -> PCon <$> fromQName qname <*> mapM fromPat ps
  PInfixApp p1 qname p2 ->
    (\n a b -> PCon n [a,b]) <$> fromQName qname <*> fromPat p1 <*> fromPat p2
  PatTypeSig loc p ty -> do
    warn $ "Ignored type signature in pattern " ++ prettyPrint pat
    fromPat p
  PAsPat name p -> do
    fatal $ "No handling of as patterns: " ++ prettyPrint pat
  _ -> do
    fatal $ "No handling for pattern: " ++ show pat ++ "\n\n" ++ prettyPrint pat

----------------------------------------------------------------------
-- Binds, i.e where

fromBinds :: Binds -> FH ()
fromBinds (BDecls []) = return ()
fromBinds (BDecls xs) =
  warn $ "Not producing any binds for where clause: " ++ show xs
fromBinds b@(IPBinds xs) =
  warn $ "Not handling implicit arguments: " ++ show b

----------------------------------------------------------------------
-- Extracting names

matchName :: Match -> H.Name
matchName (Match _ name _ _ _ _) = name

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

fromQualConDecl :: QualConDecl -> FH (Name,Int)
fromQualConDecl (QualConDecl loc tyvars cxtx condecl) = fromConDecl condecl

fromConDecl :: ConDecl -> FH (Name,Int)
fromConDecl c = case c of
  ConDecl name bangtypes                  -> return (fromName name,length bangtypes)
  InfixConDecl _bangtype1 name _bangtype2 -> return (fromName name,2)
  RecDecl name namedbangtypes             -> do
      warn $ "not creating projection declarations (" ++ fromName name ++ ")"
      return (fromName name,length namedbangtypes)
