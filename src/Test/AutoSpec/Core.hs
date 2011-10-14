module Test.AutoSpec.Core where

type Name = String
type Cons = String

-- The difference between ExtendedCore and Core is that ExtendedCore
-- can have nested patterns

newtype NestedPat = NP { denest :: ExtPattern }
  deriving (Eq,Ord,Show)

type CorePattern = Pattern Name
type ExtPattern  = Pattern NestedPat

data Pattern k = PVar Name 
               | PApp Cons [k]
  deriving (Eq,Ord,Show)

---- Declarations

type CoreDecl = Decl Name
type ExtDecl  = Decl NestedPat

data Decl k    = Fun Name [Name] (Expr k)
  deriving (Eq,Ord,Show)

type CoreExpr = Expr Name
type ExtExpr  = Expr NestedPat

data Expr k    = Let Name (Expr k) (Expr k)
               | Case Name [Branch k]
               | App (Expr k) (Expr k)
               | Cons (Expr k) (Expr k)
  deriving (Eq,Ord,Show)

type CoreBranch = Branch Name
type ExtBranch  = Branch NestedPat

data Branch k  = Branch (Pattern k) (Expr k)
  deriving (Eq,Ord,Show)