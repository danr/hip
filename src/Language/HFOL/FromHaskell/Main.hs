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

import Data.List (groupBy,(\\))
import Data.Function (on)
import Data.Maybe (fromMaybe)

run :: FilePath -> IO ()
run f = do
  r <- parseFile f
  case r of
    ParseOk m -> do
      let (res,msgs) = runFH (fromModule m)
      mapM_ putStrLn msgs
      putStrLn ""
      case res of
        Left err -> putStrLn err
        Right ds -> mapM_ (putStrLn . prettyCore) ds
    ParseFailed loc s -> putStrLn $ show loc ++ ": " ++ s

indented :: String -> String
indented = unlines . map ("    " ++) . lines

fromModule :: Module -> FH ()
fromModule (Module _loc _name _pragmas _warnings _exports _imports decls) = do
  mapM_ addTopScope decls
  mapM_ fromDecl decls

addTopScope :: Decl -> FH ()
addTopScope d = case d of
  FunBind ms -> forM_ ms $ \(Match _ mn _ _ _ _) -> let n = fromName mn
                                                     in addToScope n
  PatBind _ (H.PVar mn) _ _ _ -> let n = fromName mn in addToScope n
  _ -> return ()

fromDecl :: Decl -> FH ()
fromDecl d = case d of
  DataDecl _loc _dataornew _ctxt _name _tyvars qualcondecls _derives ->
    (decl . Data) =<< mapM fromQualConDecl qualcondecls
  FunBind matches -> fromMatches matches
  PatBind{}       -> fromPatBind d
  e -> do
    warn $ "Nothing produced for declaration: \n" ++ indented (prettyPrint e)
    write $ indented (show e)

-- Functions ------------------------------------------------------------------

fromMatches :: [Match] -> FH ()
fromMatches = mapM_ fromFunMatches . groupBy ((==) `on` matchName)

fromPatBind :: Decl -> FH ()
fromPatBind (PatBind loc (H.PVar n) mtype rhs bs) = do
  fromFunMatches [Match loc n [] mtype rhs bs]
  return ()
fromPatBind pb@(PatBind{}) =
  fatal $ "Top level patterns not supported : " ++ prettyPrint pb
fromPatBind d = fatal $ "Internal error, fromPatBind on decl " ++ show d

fromFunMatches :: [Match] -> FH Exp
fromFunMatches [] = fatal "Empty funmatches"
fromFunMatches ms@(m:_) = do
    let n = fromName (matchName m)
    fvs <- (\\) <$> freeVarss ms <*> ((n:) <$> namesInScope)
    scopedname <- scopePrefix n
    e <- addBind n scopedname fvs
    addToScope scopedname
    mapM_ addToScope fvs
    debug $ scopedname ++ " free vars: " ++ unwords fvs
    matrix <- localScopeName n
                (map (addToPats fvs) <$> concatMapM matchToRow ms)
    if null matrix
        then warn $ "Empty matrix from " ++ n
        else decl (funcMatrix scopedname matrix)
    return e
  where
    addToPats vars (ps,g,e) = (map C.PVar vars ++ ps,g,e)

matchToRow :: Match -> FH [([Pattern],Maybe Expr,Expr)]
matchToRow (Match _loc _name ps _mtype rhs bs) = localBindScope $ do
  localScopeName "where" (fromBinds bs)
  ps' <- mapM fromPat ps
  case rhs of
    UnGuardedRhs e -> do e' <- fromExp e
                         return [(ps',Nothing,e')]
    GuardedRhss gs -> forM gs $ \(GuardedRhs _loc stmts e) -> do
                                     g <- fromGuardStmts stmts
                                     e' <- fromExp e
                                     return (ps',Just g,e')

-- Case -----------------------------------------------------------------------

fromCase :: [Alt] -> FH Exp
fromCase alts = localBindScope $ fromFunMatches (map altToMatch alts)
  where
    altToMatch :: Alt -> Match
    altToMatch (Alt loc pat guardedAlt bs) =
       Match loc (Ident "case") [pat]
             (error "fromCase: maybe type")
             (toRhs guardedAlt) bs

    toRhs :: GuardedAlts -> Rhs
    toRhs (UnGuardedAlt e) = UnGuardedRhs e
    toRhs (GuardedAlts gs) = GuardedRhss (map toGuardedRhs gs)

    toGuardedRhs :: GuardedAlt -> GuardedRhs
    toGuardedRhs (GuardedAlt loc ss e) = GuardedRhs loc ss e

-- Guards ---------------------------------------------------------------------

fromGuardStmts :: [Stmt] -> FH Expr
fromGuardStmts ss = case mapM unQualify ss of
     Nothing -> fatal $ "Cannot handle these guard statements: " ++ show ss
     Just es -> foldr1 (\e1 e2 -> C.App "&&" [e1,e2]) <$> mapM fromExp es
  where
    -- No handling of let, arrow recs or pattern guards
    unQualify :: Stmt -> Maybe Exp
    unQualify (Qualifier e) = Just e
    unQualify _             = Nothing

-- Binds, i.e where -----------------------------------------------------------

fromBinds :: Binds -> FH ()
fromBinds (BDecls ds) = mapM_ fromDecl ds
fromBinds b@(IPBinds{}) =
  warn $ "Not handling implicit arguments: " ++ show b

-- Expressions ----------------------------------------------------------------

fromExp :: Exp -> FH Expr
fromExp ex = case ex of
  H.Var qn           -> mkVar =<< fromQName qn
  H.Con qn           -> con0  <$> fromQName qn
  H.App e1 e2        -> C.app <$> fromExp e1 <*> fromExp e2
  Paren e            -> fromExp e
  InfixApp e1 qop e2 -> (app .) . app <$> fromQOp qop <*> fromExp e1
                                                      <*> fromExp e2
  Lambda _loc _ps _e -> fatal "No lambda"
  H.Case e alts      -> fromExp =<< ((`H.App` e) <$> fromCase alts)
  Let bs e           -> localBindScope $ do
                            localScopeName "let" (fromBinds bs)
                            fromExp e
  Tuple es           -> C.Con (tupleName (length es)) <$> mapM fromExp es
  List es            -> listExp es
  If e1 e2 e3        -> (app .) . app . app (C.Var "if")
                          <$> fromExp e1 <*> fromExp e2 <*> fromExp e3
  _ -> fatal $ "No handling of exp " ++ prettyPrint ex ++ "\n\n" ++ show ex

listExp :: [Exp] -> FH Expr
listExp es = foldr (\x xs -> C.Con consName [x,xs]) (con0 nilName)
          <$> mapM fromExp es

mkVar :: Name -> FH Expr
mkVar n = do b <- lookupBind n
             case b of
               Nothing -> return (C.Var n)
               Just e  -> fromExp e

fromQOp :: QOp -> FH Expr
fromQOp (QVarOp qname) = mkVar =<< fromQName qname
fromQOp (QConOp qname) = con0  <$> fromQName qname

-- Patterns -------------------------------------------------------------------

fromPat :: Pat -> FH Pattern
fromPat pat = case pat of
  H.PVar pn     -> do debug $ "Är du redan bunden, lille vän? " ++ show pn
                      let n = fromName pn
                      b <- inScope n
                      if b then do n' <- scopePrefix n
                                   addBind n n' []
                                   return (C.PVar n')
                           else return (C.PVar n)
  PTuple ps     -> PCon (tupleName (length ps)) <$> mapM fromPat ps
  PList ps      -> listPattern ps
  PParen p      -> fromPat p
  PWildCard     -> return PWild
  PApp qname ps -> PCon <$> fromQName qname <*> mapM fromPat ps
  PInfixApp p1 qname p2 ->
    (\n a b -> PCon n [a,b]) <$> fromQName qname <*> fromPat p1 <*> fromPat p2
  PatTypeSig _loc p _ty -> do
    warn $ "Ignored type signature in pattern " ++ prettyPrint pat
    fromPat p
  PAsPat _n _p ->
    fatal $ "No handling of as patterns: " ++ prettyPrint pat
  _ -> fatal $ "No handling for pat: " ++ show pat ++ "\n\n" ++ prettyPrint pat

listPattern :: [Pat] -> FH Pattern
listPattern ps = foldr (\x xs -> PCon consName [x,xs]) (pcon0 nilName)
              <$> mapM fromPat ps
