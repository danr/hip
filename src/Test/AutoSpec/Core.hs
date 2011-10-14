{-# LANGUAGE DeriveDataTypeable,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances
             #-}          
module Test.AutoSpec.Core where

import Data.Data
import Data.Generics.Uniplate.Operations
import Data.Generics.Uniplate.Data

type Name = String

-- The difference between ExtendedCore and Core is that ExtendedCore
-- can have nested patterns

newtype NestedPat = NP { denest :: ExtPattern }
  deriving (Eq,Ord,Show,Data,Typeable)

type CorePattern = Pattern Name
type ExtPattern  = Pattern NestedPat

data Pattern k = PVar  Name 
               | PCons Name [k]
  deriving (Eq,Ord,Show,Data,Typeable)

varPat,conPat :: Pattern k -> Bool
varPat (PVar _) = True
varPat _        = False
conPat = not . varPat

---- Declarations

type CoreDecl = Decl Name
type ExtDecl  = Decl NestedPat

data Decl k    = Fun Name [Name] (Expr k)
  deriving (Eq,Ord,Show,Data,Typeable)

type CoreExpr = Expr Name
type ExtExpr  = Expr NestedPat

data Expr k    = Let  Name (Expr k) (Expr k)
               | Case Name [Branch k]
               | App  (Expr k) (Expr k)
               | Cons Name [Expr k]
               | Var  Name
               | Fail
  deriving (Eq,Ord,Show,Data,Typeable)

type CoreBranch = Branch Name
type ExtBranch  = Branch NestedPat

data Branch k  = Branch (Pattern k) (Expr k)
  deriving (Eq,Ord,Show,Data,Typeable)

class Subst t where
  subst :: Data k => Name -> Name -> t k -> t k

instance Subst Expr where
  subst xold xnew = transform f
    where f (Var x)      | x == xold = Var xnew
          f (Case x brs) | x == xold = Case xnew brs
          f e            = e