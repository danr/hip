module Hip.ToFOL.NecessaryDefinitions where

import Hip.ToFOL.ParserInternals
import Hip.ToFOL.Core
import Hip.ToFOL.Constructors

import Data.List
import Data.Maybe
import Control.Arrow ((***),second)

import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map as M
import Data.Map (Map)

import Data.Generics.Uniplate.Operations

-- | Given a list of used functions, returns all relevant declarations.
declsWith :: [Name] -> [Decl] -> [Decl]
declsWith ns ds = undefined

-- | Is this function is self-recursive?
selfRecursive :: Decl -> Bool
selfRecursive (Func name args body) = name `S.member` usedFs body
selfRecursive _ = error "selfRecursive: on non-function declaration"

-- Funs and Cons
class FC a where
   usedFC :: a -> (Set Name,Set Name)

usedFs :: FC a => a -> Set Name
usedFs = fst . usedFC

-- Wow, these two functions should use some graph library, really

-- | Which functions call this functions, transitively?
callers :: [Decl] -> Set Name -> Set Name
callers funDecls = go
  where
    -- For each function, which functions does it call in one step?
    usedFss :: [(Name,Set Name)]
    usedFss = [ (declName d,usedFs d) | d <- funDecls ]

    -- For each function, which function calls it in one step?
    callsMap :: Map Name (Set Name)
    callsMap = M.fromList
               [ (n,S.fromList (map fst (filter (S.member n . snd) usedFss)))
               | d <- funDecls
               , let n = declName d
               ]

    safeLookup :: Name -> Set Name
    safeLookup f = fromMaybe S.empty (M.lookup f callsMap)

    go fs | S.null newfs = fs
          | otherwise    = go (fs `S.union` fs')
      -- Get the new functions from here
      where fs' :: Set Name
            fs' = S.unions (map safeLookup (S.toList fs))
            newfs = fs' S.\\ fs

-- | Which functions do this set of functions call, transitively?
iterateFCs :: [Decl] -> Set Name -> (Set Name,Set Name)
iterateFCs funDecls = go
  where
    usedFCmap :: Map Name (Set Name,Set Name)
    usedFCmap = M.fromList [ (declName d,usedFC d) | d <- funDecls ]

    safeLookup :: Name -> (Set Name,Set Name)
    safeLookup f = fromMaybe (S.empty,S.empty) (M.lookup f usedFCmap)

    go fs | S.null newfs = (fs,cs)
          | otherwise    = go (fs `S.union` fs')
      -- Get the new functions from here
      where fs',cs :: Set Name
            (fs',cs) = (S.unions *** S.unions)
                       (unzip (map safeLookup (S.toList fs)))
            newfs = fs' S.\\ fs

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

