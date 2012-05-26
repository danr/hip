{-# LANGUAGE DeriveDataTypeable #-}
module Hip.Trans.Core where

import Data.Data
import Data.Generics.Uniplate.Data

import Var

type Name = String

data Expr = App Var [Expr]
          | Con Var [Expr]
          | Var Var
          | Expr ::: Type
          -- ^ Used in instantiating induction schemas
  deriving(Eq,Ord,Data,Typeable)

-- Cannot handle type var applications, as f in : (a -> b) -> f a -> f b
data Type = TyVar Name
          | TyFun [Type]
          | TyCon Name [Type]
  deriving(Eq,Ord,Data,Typeable)

-- Auxiliary functions

isTyVar :: Type -> Bool
isTyVar TyVar{} = True
isTyVar _       = False

-- | Transforms applications to the function/constructor name with an
--   argument list.
app :: Expr -> Expr -> Expr
app (App n es) e = App n (es ++ [e])
app (Con n es) e = Con n (es ++ [e])
app (Var n)    e = App n [e]
app IsBottom{} _ = error "app on IsBottom"

infixl `app`

tapp :: Type -> Type -> Type
tapp t (TyFun []) = t
tapp t (TyFun ts) = TyFun (t:ts)
tapp t t2         = TyFun [t,t2]

tconapp :: Type -> Type -> Maybe Type
tconapp (TyCon n ts) t = Just (TyCon n (ts ++ [t]))
tconapp _            t = Nothing

infixr `tapp` `tconapp`

-- | Nullary constructor
con0 :: Name -> Expr
con0 n = Con n []

-- | Nullary type constructor
tycon0 :: Name -> Type
tycon0 n = TyCon n []

-- | Type variables in a type
tyVars :: Type -> [Name]
tyVars t = [ x | TyVar x <- universe t ]

-- | Substitution
subst :: Name -> Name -> Expr -> Expr
subst xold xnew = transform f
  where f (Var x)    | x == xold = Var xnew
        f (App x as) | x == xold = App xnew as
        f e = e

-- | Substitute a list of variables
substVars :: [(Name,Name)] -> Expr -> Expr
substVars ns e = foldr (\(x,x') -> subst x x') e ns

-- | Substitute a list of variables in the body
substVarsBody :: [(Name,Name)] -> Body -> Body
substVarsBody ns e = foldr (\(x,x') -> substBody x x') e ns

-- | Concrete types are types like Nat, Tree a, but not a or Nat -> Nat
concreteType :: Type -> Bool
concreteType TyCon{} = True
concreteType _       = False

-- | Strips an expression of its types
stripTypes :: Expr -> Expr
stripTypes = transform f
  where
    f (e ::: t) = e
    f e         = e

-- | The result of a type function
resType :: Type -> Type
resType t = case t of TyApp ts -> last ts
                      _        -> t

-- | Type of the arguments to a function
argsTypes :: Type -> [Type]
argsTypes t = case t of TyApp ts -> init ts
                        _        -> []

-- | Removes the type constructor if there is one. Used for removing Prop
unProp :: Type -> Type
unProp (TyCon _ [t]) = t
unProp t             = t

-- | Which arguments to this constructor are recursive?
--
--   For example, Branch :: Tree a -> a -> Tree a -> Tree a is
--   recursive in its first and third argument, as it is the same as
--   the resulting type, so the result of this function will be
--   [True,False,True]
recursiveArgs :: Type -> [Bool]
recursiveArgs (TyApp ts) = let resType = last ts
                           in  map (== resType) (init ts)
recursiveArgs _          = []

