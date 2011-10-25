{-# LANGUAGE DeriveDataTypeable #-}
module Language.HFOL.Core where

-- TODO : Add guards!

import Data.Data

type Name = String

data Decl = Func { funcName :: Name
                 , funcArgs :: [Name]
                 , funcBody :: Body
                 }
  deriving(Eq,Ord,Data,Typeable)

data Body = Case { caseScrutinee :: Expr
                 , caseBranches :: [Branch]
                 }
          | Expr Expr
  deriving(Eq,Ord,Data,Typeable)

data Expr = App { exprName :: Name , exprArgs :: [Expr] }
          | Con { exprName :: Name , exprArgs :: [Expr] }
          | Var { exprName :: Name }
  deriving(Eq,Ord,Data,Typeable)



infix 7 :->

data Branch = (:->) { brPat :: Pattern , brExpr :: Expr }
  deriving(Eq,Ord,Data,Typeable)


data Pattern = PVar { patName :: Name }
             | PCon { patName :: Name, patArgs :: [Pattern] }
             | PWild
  deriving(Eq,Ord,Data,Typeable)

-- Auxiliary functions

-- | The three kinds of patterns
varPat,conPat,wildPat :: Pattern -> Bool
varPat (PVar _)   = True
varPat _          = False
conPat (PCon _ _) = True
conPat _          = False
wildPat PWild     = True
wildPat _         = False

-- | Costructor pattern without arguments
con0Pat :: Pattern -> Bool
con0Pat (PCon _ []) = True
con0Pat _           = False

-- | Transforms applications to the function/constructor name with an
--   argument list.
app :: Expr -> Expr -> Expr
app (App n es) e = App n (es ++ [e])
app (Con n es) e = Con n (es ++ [e])
app (Var n)    e = App n [e]

-- | Nullary constructor
con0 :: Name -> Expr
con0 n = Con n []

-- | Nullary constructor pattern
pcon0 :: Name -> Pattern
pcon0 n = PCon n []

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
                                  (map (\(as,e) -> PCon tup as :-> e) m)
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
                              (map (\(p :-> e) -> PCon tup (p : as) :-> e) brs)
  where len = length as
        us  = [ 'u':show x | x <- [1..len] ]
        tup = "Tup" ++ show (len + 1)

