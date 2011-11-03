module Language.HFOL.FromHaskell where

import qualified Language.Haskell.Exts as H
import Language.Haskell.Exts hiding (Name,app)

import qualified Language.HFOL.Core as C
import Language.HFOL.Core hiding (Decl)

import Language.HFOL.FromHaskell.Names
import Language.HFOL.FromHaskell.Monad
import Language.HFOL.FromHaskell.Vars

import Language.HFOL.Pretty

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.RWS hiding (gets,modify,local,asks)
import Data.Label.PureM

import Data.List (groupBy,(\\))
import Data.Function (on)
import Data.Maybe (fromMaybe)

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
fromModule (Module loc name pragmas warnings exports imports decls) = do
  mapM_ addToScope decls
  mapM_ fromDecl decls

addToScope :: Decl -> FH ()
addToScope d = case d of
  FunBind ms -> forM_ ms $ \(Match _ mn _ _ _ _) -> let n = fromName mn
                                                     in addBind n n []
  PatBind _ (H.PVar mn) _ _ _ -> let n = fromName mn in addBind n n []
  _ -> return ()

fromDecl :: Decl -> FH ()
fromDecl d = case d of
  DataDecl loc dataornew ctxt name tyvars qualcondecls derives ->
    (decl . Data) =<< mapM fromQualConDecl qualcondecls
  FunBind matches -> fromMatches matches
  PatBind{}       -> fromPatBind d
  e -> do
    warn $ "Nothing produced for declaration: \n" ++ indented (prettyPrint e)
    write $ indented (show e)

-- Functions -------------------------------------------------------------------

fromMatches :: [Match] -> FH ()
fromMatches = mapM_ fromFunMatches . groupBy ((==) `on` matchName)

fromFunMatches :: [Match] -> FH ()
fromFunMatches [] = warn $ "Empty funmatches"
fromFunMatches ms@(m:_) = do
    let name = fromName (matchName m)
    fvs <- (\\) <$> concatMapM freeVars ms <*> namesInScope
    scopedname <- scopePrefix name
    addBind name scopedname fvs
    debug $ scopedname ++ " free vars: " ++ unwords fvs
    matrix <- localScopeName name (map (addToPats fvs) <$> concatMapM matchToRow ms)
    if null matrix
        then warn $ "Empty matrix from " ++ name
        else decl (funcMatrix scopedname matrix)
  where
    addToPats vars (ps,g,e) = (map C.PVar vars ++ ps,g,e)


fromPatBind :: Decl -> FH ()
fromPatBind (PatBind loc (H.PVar name) mtype rhs binds) =
  fromFunMatches [Match loc name [] mtype rhs binds]
fromPatBind pb@(PatBind loc p mtype rhs binds) =
  fatal $ "Top level patterns not supported : " ++ prettyPrint pb
fromPatBind d = fatal $ "Internal error, fromPatBind on decl " ++ show d

matchToRow :: Match -> FH [([Pattern],Maybe Expr,Expr)]
matchToRow (Match loc name ps mtype rhs binds) = localBindScope $ do
  localScopeName "where" (fromBinds binds)
  ps' <- mapM fromPat ps
  case rhs of
    UnGuardedRhs e -> do e' <- fromExp e
                         return [(ps',Nothing,e')]
    GuardedRhss gs -> forM gs $ \(GuardedRhs _loc stmts e) -> do
                                     g <- fromGuardStmts stmts
                                     e' <- fromExp e
                                     return (ps',Just g,e')

-- Guards ----------------------------------------------------------------------

fromGuardStmts :: [Stmt] -> FH Expr
fromGuardStmts ss = case sequence (map unQualify ss) of
     Nothing -> fatal $ "Cannot handle these guard statements: " ++ show ss
     Just es -> foldr1 (\e1 e2 -> C.App "&&" [e1,e2]) <$> mapM fromExp es
  where
    -- No handling of let, arrow recs or pattern guards
    unQualify :: Stmt -> Maybe Exp
    unQualify (Qualifier e) = Just e
    unQualify _             = Nothing

-- Binds, i.e where ------------------------------------------------------------

fromBinds :: Binds -> FH ()
fromBinds (BDecls ds) = mapM_ fromDecl ds
fromBinds b@(IPBinds xs) =
  warn $ "Not handling implicit arguments: " ++ show b

-- Expressions -----------------------------------------------------------------

fromExp :: Exp -> FH Expr
fromExp e = case e of
  H.Var qn           -> mkVar =<< fromQName qn
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

mkVar :: Name -> FH Expr
mkVar n = fromMaybe (C.Var n) <$> lookupBind n

fromQOp :: QOp -> FH Expr
fromQOp (QVarOp qname) = mkVar =<< fromQName qname
fromQOp (QConOp qname) = con0  <$> fromQName qname

-- Patterns --------------------------------------------------------------------

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

