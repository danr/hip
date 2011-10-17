{-# LANGUAGE DeriveDataTypeable #-}          
module Test.AutoSpec.Core where

import Data.Data

type Name = String

-- The difference between ExtendedCore and Core is that ExtendedCore
-- can have nested patterns

newtype NestedPat = NP { denest :: ExtPattern }
  deriving (Eq,Ord,Show,Data,Typeable)

type CorePattern = Pattern Name
type ExtPattern  = Pattern NestedPat

data Pattern k = PVar  { patName :: Name }
               | PCons { patName :: Name , patArgs :: [k] }
  deriving (Eq,Ord,Show,Data,Typeable)

varPat,conPat :: Pattern k -> Bool
varPat (PVar _) = True
varPat _        = False
conPat = not . varPat

---- Declarations

type CoreDecl = Decl Name
type ExtDecl  = Decl NestedPat

data Decl k   = Fun { funName :: Name , funArgs :: [k] , funExpr :: Expr k }
  deriving (Eq,Ord,Show,Data,Typeable)

type CoreExpr = Expr Name
type ExtExpr  = Expr NestedPat

data Expr k    = Case Name [Branch k]
               | App  (Expr k) (Expr k)
               | Cons Name [Expr k]
               | Var  Name
               | Fail
               | Expr k :| Expr k
  deriving (Eq,Ord,Show,Data,Typeable)

app :: Expr k -> Expr k -> Expr k
app (Cons n es) e  = Cons n (es ++ [e])
app e1          e2 = App e1 e2
  
type CoreBranch = Branch Name
type ExtBranch  = Branch NestedPat

data Branch k  = Branch { branchPat :: Pattern k , branchExpr :: Expr k }
  deriving (Eq,Ord,Show,Data,Typeable)

