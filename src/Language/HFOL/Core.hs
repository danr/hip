{-# LANGUAGE DeriveDataTypeable #-}
module Language.HFOL.Core where

import Data.Data
import Data.Generics.Uniplate.Data

type Name = String

data Decl = Func { funcName :: Name
                 , funcArgs :: [Name]
                 , funcBody :: Body
                 }
          | Data { dataCons :: [(Name,Int)] }
  deriving(Eq,Ord,Data,Typeable)

data Body = Case { caseScrutinee :: Expr
                 , caseBranches :: [Branch]
                 }
          | Expr Expr
  deriving(Eq,Ord,Data,Typeable)

data Expr = App { exprName :: Name , exprArgs :: [Expr] }
          | Con { exprName :: Name , exprArgs :: [Expr] }
          | Var { exprName :: Name }
          | IsBottom Expr
            -- ^ For guards that evaluate to bottom
  deriving(Eq,Ord,Data,Typeable)

infix 7 :->

data Branch = (:->) { brPMG :: PMG , brExpr :: Expr }
  deriving(Eq,Ord,Data,Typeable)

-- Pattern + Maybe Guard
data PMG = NoGuard { pattern :: Pattern }
         | Guard   { pattern :: Pattern , guardExpr :: Expr }
  deriving(Eq,Ord,Data,Typeable)

data Pattern = PVar { patName :: Name }
             | PCon { patName :: Name , patArgs :: [Pattern] }
             | PWild
  deriving(Eq,Ord,Data,Typeable)

-- Auxiliary functions

-- | Modify the pattern of a PMG
modifyPattern :: (Pattern -> Pattern) -> PMG -> PMG
modifyPattern f (Guard p e) = Guard (f p) e
modifyPattern f (NoGuard p) = NoGuard (f p)

-- | Modify the guard of a PMG if it exists
modifyGuard :: (Expr -> Expr) -> PMG -> PMG
modifyGuard f (Guard p e) = Guard p (f e)
modifyGuard f ng          = ng

-- | Declaration is a function declaration
funcDecl :: Decl -> Bool
funcDecl Func{} = True
funcDecl _      = False

-- | The three kinds of patterns
varPat,conPat,wildPat :: Pattern -> Bool
varPat PVar{} = True
varPat _      = False
conPat PCon{} = True
conPat _      = False
wildPat PWild = True
wildPat _     = False

-- | Costructor pattern without arguments
con0Pat :: Pattern -> Bool
con0Pat (PCon _ []) = True
con0Pat _           = False

-- | With or without guard
guarded,notGuarded :: PMG -> Bool
guarded Guard{} = True
guarded _       = False
notGuarded = not . guarded

-- | Transforms applications to the function/constructor name with an
--   argument list.
app :: Expr -> Expr -> Expr
app (App n es) e = App n (es ++ [e])
app (Con n es) e = Con n (es ++ [e])
app (Var n)    e = App n [e]
app IsBottom{} _ = error "app on IsBottom"

-- | Nullary constructor
con0 :: Name -> Expr
con0 n = Con n []

-- | Nullary constructor pattern
pcon0 :: Name -> Pattern
pcon0 n = PCon n []

-- | Free variables
class FV a where
  fv :: a -> [Name]

instance FV Expr where
  fv e = [ x | Var x <- universe e ]

instance FV Pattern where
  fv p = [ x | PVar x <- universe p ]

-- | Substitution
subst :: Name -> Expr -> Expr -> Expr
subst x' e' = transform f
  where f (Var x) | x == x' = e'
        f e       =  e

substVars :: [(Name,Name)] -> Expr -> Expr
substVars ns e = foldr (\(x,x') -> subst x (Var x')) e ns

{-
 Given a function name and the matrix of patterns and expressions,
 returns a function which cases on the arguments and branches
 on the patterns and expressions

 f p11 p12 ... p1n = e1
 ...
 f pk1 pk2 ... pkn = ek

   =>

 f u1 ... un = case Tn u1 .. un of
                   Tn p11 ... p1n -> e1
                   ...
                   Tn pk1 ... pkn -> ek

 The corresponding function call is
 funcMatrix "f" [ ( [p11,...,p1n] , e1 ), ... , ([pk1,...,pkn] , ek) ]

-}
funcMatrix :: Name -> [([Pattern],Expr)] -> Decl
funcMatrix n m = Func n us $ Case (Con tup (map Var us))
                                  [ NoGuard (PCon tup as) :-> e | (as,e) <- m ]
  where len = length (fst (head m))
        us  = [ 'u':show x | x <- [1..len] ]
        tup = "Tup" ++ show len

{-
   Expand a function definition with pattern matchings
   by prepending the pattern on the body case, or
   do the same as funcMatrix above.
-}
func :: Name -> [Pattern] -> Body -> Decl
func n as b | all varPat as || null as = Func n (map patName as) b
func n as (Expr e)     = funcMatrix n [(as,e)]
func n as (Case s brs) = Func n us $
                         Case (Con tup (s : map Var us))
                              [ modifyPattern (\p -> PCon tup (p:as)) pmg :-> e
                              | pmg :-> e <- brs ]
  where len = length as
        us  = [ 'u':show x | x <- [1..len] ]
        tup = "Tup" ++ show (len + 1)

