module Autospec.ToFOL.NecessaryDefinitions where

import Autospec.ToFOL.ParserInternals
import Autospec.ToFOL.Core
import Autospec.ToFOL.Constructors

import qualified Data.Set as S
import Data.Set (Set)
import Data.List
import Data.Maybe
import Control.Arrow ((***),second)

import Data.Generics.Uniplate.Operations

-- | Given a list of used functions, returns all relevant declarations.
declsWith :: [Name] -> [Decl] -> [Decl]
declsWith ns ds = undefined

-- | Is this function is self-recursive?
selfRecursive :: Decl -> Bool
selfRecursive (Func name args body) = name `S.member` fst (usedFC body)
selfRecursive _ = error "selfRecursive: on non-function declaration"

-- Funs and Cons
class FC a where
   usedFC :: a -> (Set Name,Set Name)

instance FC Pattern where
  usedFC p = (S.fromList [ x | PVar x <- universeBi p ]
             ,S.fromList [ x | PCon x _ <- universeBi p ]
             )

(><) :: (a -> b -> c) -> (a' -> b' -> c') -> (a,a') -> (b,b') -> (c,c')
(f >< g) (x1,y1) (x2,y2) = (x1 `f` x2,y1 `g` y2)

instance FC Branch where
  usedFC (NoGuard p :-> e) = (S.difference >< S.union) (usedFC e) (usedFC p)
  usedFC (Guard p g :-> e) = second (S.insert trueName) $
                                 (S.difference >< S.union)
                                 ((S.union >< S.union) (usedFC e) (usedFC g))
                                 (usedFC p)

instance FC Expr where
  usedFC e = (S.fromList (mapMaybe vars (universe e))
             ,S.fromList [ c | Con c _ <- universe e])
    where
      vars (App f xs) = Just f
      vars (Var x)    = Just x
      vars _          = Nothing


instance FC Body where
  usedFC (Expr e) = usedFC e
  usedFC (Case e brs) = (S.union >< S.union)
                        (usedFC e)
                        ((S.unions *** S.unions) (unzip (map usedFC brs)))

instance FC Decl where
   usedFC (Func name args body) =
      let (fs,cs) = usedFC body
      in  (S.delete name (fs S.\\ S.fromList args),cs)
   usedFC _ = (S.empty,S.empty)

