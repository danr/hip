module Language.HFOL.FromHaskell.FromHaskell (parseHaskell,run) where

import qualified Language.Haskell.Exts as H
import Language.Haskell.Exts hiding (Name,app)

import qualified Language.HFOL.ToFOL.Core as C
import Language.HFOL.ToFOL.Core hiding (Decl)

import Language.HFOL.FromHaskell.Names
import Language.HFOL.FromHaskell.Monad
import Language.HFOL.FromHaskell.Vars

import Language.HFOL.Util (concatMapM)
import Language.HFOL.ToFOL.Pretty

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

parseHaskell :: String -> (Either String [C.Decl],[String])
parseHaskell s =
  let r = parseModule s in
  case r of
    ParseOk     m     -> runFH (fromModule m)
    ParseFailed loc s -> (Left ("Parse fail " ++ show loc ++ ": " ++ s),[])

indented :: String -> String
indented = unlines . map ("    " ++) . lines

fromModule :: Module -> FH ()
fromModule (Module _loc _name _pragmas _warns _ex _im decls) = fromDecls decls

-- Removing pattern binds -----------------------------------------------------

patBindToFunBind :: Decl -> FH Decl
patBindToFunBind d = case d of
  PatBind loc (H.PVar n) mtype rhs bs -> return (FunBind [Match loc n [] mtype rhs bs])
  PatBind{} -> fatal $ "Patterns binds not supported : " ++ prettyPrint d
  _ -> return d

-- For declarations, you need to do three passes:
--
-- (1) Add all defined declarations as in scope
--
-- (2) Add an indirection to the defined name to the scoped name
--     applied to free variables
--
-- (3) Produce code

fromDecls :: [Decl] -> FH ()
fromDecls ds = do
  ds' <- mapM patBindToFunBind ds
  mapM_ addDeclScope ds'
  mapM_ addDeclIndirection ds'
  mapM_ fromDecl ds'

addDeclScope :: Decl -> FH ()
addDeclScope d = case d of
  FunBind ms -> mapM_ addMatchesScope (groupBy ((==) `on` matchName) ms)
  _ -> return ()

addDeclIndirection :: Decl -> FH ()
addDeclIndirection d = case d of
  FunBind ms -> mapM_ addMatchesIndirection (groupBy ((==) `on` matchName) ms)
  _ -> return ()

fromDecl :: Decl -> FH ()
fromDecl d = case d of
  DataDecl _loc _dataornew _ctxt _name _tyvars qualcondecls _derives ->
    (decl . Data) =<< mapM fromQualConDecl qualcondecls
  FunBind ms -> mapM_ fromMatches (groupBy ((==) `on` matchName) ms)
  PatBind{}  -> fatal $ "Internal error: PatBind in fromDecl"
  TypeSig{}  -> debug $ (prettyPrint d)
  e -> do
    warn $ "Nothing produced for declaration: \n" ++ indented (prettyPrint e)
    write $ indented (show e)

-- Functions --------------------------------------------------------------------

-- Adding scope (first pass)
addMatchesScope :: [Match] -> FH ()
addMatchesScope [] = fatal "Empty funmatches"
addMatchesScope ms@(m:_) = do
    let n = fromName (matchName m)
    addToScope n
    debug $ "addMatchesScope: " ++ n ++ " added to scope."

-- Add indirections (second pass)
addMatchesIndirection :: [Match] -> FH ()
addMatchesIndirection [] = fatal "Empty funmatches"
addMatchesIndirection ms@(m:_) = do
    let n = fromName (matchName m)
    fvs <- (\\) <$> freeVarss ms <*> namesInScope
    scopedname <- scopePrefix n

    scope <- namesInScope
    debug $ "addMatchesIndirection: " ++ scopedname ++ " free vars: "
            ++ unwords fvs ++ " (in scope: " ++ unwords scope ++ ")"

    addBind n scopedname fvs

-- Generate code (third pass)
fromMatches :: [Match] -> FH Expr
fromMatches [] = fatal "Empty funmatches"
fromMatches ms@(m:_) = do
    let n = fromName (matchName m)
    (scopedname,fvs) <- fromMaybe (error $ "fromMatches: unbound " ++ n)
                                  <$> lookupBind n

    scope <- namesInScope
    debug $ "fromMatches: " ++ scopedname ++ " free vars: " ++ unwords fvs
            ++ " (in scope: " ++ unwords scope ++ ")"

    localBindScope $ do
      -- All free variables are arguments to this function
      mapM_ addToScope fvs
      matrix <- localScopeName n
                  (map (addToPats fvs) <$> concatMapM matchToRow ms)
      if null matrix
          then warn $ "Empty matrix from " ++ n
          else decl (funcMatrix scopedname matrix)

    -- Return the expression that is this function (used by case, lambda)
    mkVar n
  where
    addToPats vars (ps,g,e) = (map C.PVar vars ++ ps,g,e)
    matchPattern (Match _ _ ps _ _ _) = ps

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

-- This is used from lambda and case
fromMatches' :: [Match] -> FH Expr
fromMatches' ms = do
  addMatchesScope ms
  addMatchesIndirection ms
  fromMatches ms

-- Case -----------------------------------------------------------------------

-- This does not yet use the C.Case
fromCase :: Exp -> [Alt] -> FH Expr
fromCase e alts = do
     caseExpr <- localBindScope $ do
                    mapM_ removeFromScope =<< freeVars e
                    fromMatches' (map altToMatch alts)
     (caseExpr `C.app`) <$> fromExp e
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
fromGuardStmts ss = case (mapM :: (Stmt -> Maybe Exp) -> [Stmt] -> Maybe [Exp])
                         unQualify ss of
     Nothing -> fatal $ "Cannot handle these guard statements: " ++ show ss
     Just es -> foldr1 (\e1 e2 -> C.App "&&" [e1,e2]) <$> mapM fromExp es
  where
    -- No handling of let, arrow recs or pattern guards
    unQualify :: Stmt -> Maybe Exp
    unQualify (Qualifier e) = Just e
    unQualify _             = Nothing

-- Binds, i.e where, let ------------------------------------------------------

fromBinds :: Binds -> FH ()
fromBinds (BDecls ds) = fromDecls ds
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
  Lambda loc ps e    -> localBindScope (fromMatches'
                        [ Match loc (Ident "lambda") ps
                                (error "fromExp: lambda maybe type")
                                (UnGuardedRhs e) (BDecls []) ])
  H.Case e alts      -> fromCase e alts
  Let bs e           -> localBindScope $ do
                            localScopeName "let" (fromBinds bs)
                            fromExp e
  Tuple es           -> C.Con (tupleName (length es)) <$> mapM fromExp es
  List es            -> listExp es
  If e1 e2 e3        -> do warn $ "Assumes if :: Bool -> a -> a -> a in scope"
                           (app .) . app . app (C.Var "if")
                             <$> fromExp e1 <*> fromExp e2 <*> fromExp e3
  RightSection op e  -> do x <- Ident <$> scopePrefix "x"
                           fromExp (Lambda (error "lambda location on rsection")
                                           [H.PVar x]
                                           (InfixApp (H.Var (UnQual x)) op e))
  LeftSection e op   -> do x <- Ident <$> scopePrefix "x"
                           fromExp (Lambda (error "lambda location on lsection")
                                           [H.PVar x]
                                           (InfixApp e op (H.Var (UnQual x))))
  _ -> fatal $ "No handling of exp " ++ prettyPrint ex ++ "\n\n" ++ show ex

listExp :: [Exp] -> FH Expr
listExp es = foldr (\x xs -> C.Con consName [x,xs]) (con0 nilName)
          <$> mapM fromExp es

mkVar :: Name -> FH Expr
mkVar n = do b <- lookupBind n
             return $ case b of
               Nothing       -> C.Var n
               Just (n,args) -> foldl C.app (C.Var n) (map C.Var args)

fromQOp :: QOp -> FH Expr
fromQOp (QVarOp qname) = mkVar =<< fromQName qname
fromQOp (QConOp qname) = con0  <$> fromQName qname

-- Patterns -------------------------------------------------------------------

fromPat :: Pat -> FH Pattern
fromPat pat = case pat of
  H.PVar pn     -> do -- debug $ "Check if in scope: " ++ show pn
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