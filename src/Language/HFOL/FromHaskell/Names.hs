module Language.HFOL.FromHaskell.Names where

import Language.HFOL.FromHaskell.Monad
import Language.HFOL.Core(Name)
import qualified Language.Haskell.Exts as H
import Language.Haskell.Exts hiding (Name,name)
import Control.Monad

----------------------------------------------------------------------
-- Extracting names

matchName :: Match -> H.Name
matchName (Match _ name _ _ _ _) = name

fromName :: H.Name -> Name
fromName (Ident s)  = s
fromName (Symbol s) = s

fromQName :: QName -> FH Name
fromQName q@(Qual _modulename name) = do
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
  return ('T':show n)
fromSpecial Cons    = return ":"
fromSpecial UnboxedSingleCon = do
  warn "No handling of unboxed singleton constructor"
  return "()"

fromQualConDecl :: QualConDecl -> FH (Name,Int)
fromQualConDecl (QualConDecl _loc _tyvars _cxtx condecl) = fromConDecl condecl

fromConDecl :: ConDecl -> FH (Name,Int)
fromConDecl c = case c of
  ConDecl name bangts               -> return (fromName name,length bangts)
  InfixConDecl _bangt1 name _bangt2 -> return (fromName name,2)
  RecDecl name namedbangtypes       -> do
      warn $ "not creating projection declarations (" ++ fromName name ++ ")"
      return (fromName name,length namedbangtypes)
