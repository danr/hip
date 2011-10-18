{-# LANGUAGE DeriveDataTypeable #-}
module Language.HFOL.Core where

import Data.Data

type Name = String

data Decl = Func { funcName :: Name
                 , funcArgs :: [Name]
                 , funcBody :: Body
                 }
  deriving(Eq,Ord,Show,Data,Typeable)

data Body = Case { scrutinee :: Expr
                 , branches :: [Branch]
                 }
          | Expr Expr
  deriving(Eq,Ord,Show,Data,Typeable)

data Expr = App Expr Expr
          | Con Name [Expr]
          | Var Name
  deriving(Eq,Ord,Show,Data,Typeable)

data Branch = Pattern :-> Expr
  deriving(Eq,Ord,Show,Data,Typeable)

data Pattern = PVar { patName :: Name }
             | PCon { patName :: Name, patArgs :: [Pattern] }
             | Default
  deriving(Eq,Ord,Show,Data,Typeable)

app :: Expr -> Expr -> Expr
app (Con n es) e  = Con n (es ++ [e])
app e1         e2 = App e1 e2

pcon0 :: Name -> Pattern
pcon0 n = PCon n []

con0 :: Name -> Expr
con0 n = Con n []
