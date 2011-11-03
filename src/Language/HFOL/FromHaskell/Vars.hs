module Language.HFOL.FromHaskell.Vars where

import qualified Language.HFOL.Core as C
import Language.Haskell.Exts
import Language.HFOL.FromHaskell.Monad
import Language.HFOL.FromHaskell.Names

import Data.Set as S

import Control.Applicative hiding (empty)

class FV a where
  fv :: a -> FH (Set C.Name)

freeVars :: FV a => a -> FH [C.Name]
freeVars = fmap S.toList . fv

fvs :: FV a => [a] -> FH (Set C.Name)
fvs = fmap unions . mapM fv

none :: FH (Set C.Name)
none = return empty

instance FV Exp where
  fv e = case e of
      Var qn                     -> singleton <$> fromQName qn
      Con{}                      -> none
      Lit{}                      -> none
      InfixApp e1 (QVarOp qn) e2 -> unions <$> sequence [singleton <$> fromQName qn,fv e1,fv e2]
      InfixApp{}                 -> none
      App e1 e2                  -> union <$> fv e1 <*> fv e2
      Lambda _loc ps el          -> difference <$> fv el <*> fvs ps
      If e1 e2 e3                -> unions <$> mapM fv [e1,e2,e3]
      Case e alts                -> union <$> fv e <*> fvs alts
      _                          -> fatal $ "FV on exp " ++ show e

instance FV Decl where
  fv d = case d of
    FunBind ms -> fvs ms
    PatBind loc (PVar name) mtype rhs binds -> fv (Match loc name [] mtype rhs binds)
    PatBind _loc p _mtype _rhs _binds -> fatal $ "FV on top level pattern: " ++ show p

instance FV Match where
  fv (Match _loc name ps _mtype rhs binds) = do
     rhsvs   <- fv rhs
     psvs    <- fvs ps
     bindsvs <- fv binds
     -- Is this correct? Take all FV of the rhsvs and the binds, minus
     -- those from the patterns
     return $ (rhsvs `union` bindsvs) `difference` psvs

instance FV Rhs where
  fv (UnGuardedRhs e) = fv e
  fv (GuardedRhss gs) = fvs gs

instance FV GuardedRhs where
  fv (GuardedRhs _loc stmts e) = union <$> fvs stmts <*> fv e

instance FV Alt where
  fv (Alt _loc pat guarded binds) = do
    patvs   <- fv pat
    guardvs <- fv guarded
    bindsvs <- fv binds
    return $ (guardvs `union` bindsvs) `difference` patvs

instance FV GuardedAlts where
  fv (UnGuardedAlt e) = fv e
  fv (GuardedAlts gs) = fvs gs

instance FV GuardedAlt where
  fv (GuardedAlt _loc stmts e) = union <$> fvs stmts <*> fv e

-- Only interpreting Stmt as a guard!
instance FV Stmt where
  fv (Generator _loc p _e) = fatal $ "Pattern guards not supported: " ++ show p
  fv (Qualifier e)         = fv e
  fv (LetStmt binds)       = fv binds
  fv (RecStmt _stmts)      = fatal $ "Rec statements not supported"

instance FV Binds where
  fv (BDecls ds) = fvs ds
  fv (IPBinds{}) = warn "Not handling implicit arguments" >> none

-- These are not really free vars, they are bound vars, but they work the same way
instance FV Pat where
  fv p = case p of
    PVar name           -> return (singleton (fromName name))
    PLit{}              -> none
    PNeg{}              -> none
    PInfixApp p1 _qn p2 -> union <$> fv p1 <*> fv p2
    PApp _qn ps         -> fvs ps
    PTuple ps           -> fvs ps
    PList ps            -> fvs ps
    PParen p            -> fv p
    PWildCard           -> none
    _                   -> fatal $ "FV on pat " ++ show p