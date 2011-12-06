module Autospec.ToFOL.FixpointInduction where

import Autospec.ToFOL.ParserInternals
import Autospec.ToFOL.Core
import Autospec.ToFOL.Pretty
import Autospec.Util
import Autospec.ToFOL.NecessaryDefinitions

import Control.Arrow
import Control.Monad

import qualified Data.Set as S
import Data.Set (Set)

import Data.Maybe

exampleCode :: [Decl]
exampleCode = parseDecls $ concatMap (++ ";")
  [ "even Z     = True"
  , "even (S x) = not (odd x)"
  , "odd Z      = True"
  , "odd (S x)  = not (even x)"
  ]

exampleCode2 = parseDecls $ unlines
 [ "qs0 f q0 xs = scanr f q0 xs ;"
 , "cs2 u1 u2 u3 u4 = case T4 u1 u2 u3 u4 of {"
 , "                           T4 f q0 xs (Cons q3 w) -> q3"
 , "                       } ;"
 , "q1 f q0 xs = cs2 f q0 xs (qs0 f q0 xs) ;"
 , "scanr u1 u2 u3 = case T3 u1 u2 u3 of {"
 , "                      T3 f q0 Nil -> Cons q0 Nil;"
 , "                      T3 f q0 (Cons x xs) -> Cons (f x (q1 f q0 xs)) (qs0 f q0 xs)"
 , "                  } ;"
 ]

-- Lifts the functions up for suitable fixpoint induction Assumes all
-- decls are fundecls, and that the functions are recursive.
--
-- Algorithm for lifting fs of definitions ds:
--     Find all functions rs that use those in fs. The functions fs
--     are necessarily members there.
--     For all functions in rs, make new decls where the function f
--     is defined as f.fixMe, and all calls to f are now called f.unRec
fixate :: [Name] -> [Decl] -> [Decl]
fixate fs ds = mapMaybe mod ds
  where
    fset    :: Set Name
    fset    = S.fromList fs

    rs      :: Set Name
    rs      = callers ds fset

    fsUnRec :: [(Name,Name)]
    fsUnRec = map (id &&& (++ ".unRec")) fs

    restNames :: [(Name,Name)]
    restNames = map (id &&& (++ ".copy")) (S.toList (rs S.\\ fset))

    substList :: [(Name,Name)]
    substList = fsUnRec ++ restNames

    mod :: Decl -> Maybe Decl
    mod (Func name args body) = do
        guard (not $ S.null $ rs `S.intersection` (S.insert name (usedFs body)))
        return $ Func (fromMaybe (error $ "fixate: " ++ name ++ "lost")
                                 (lookup name substList))
                      args
                      (substVarsBody substList body)
    mod _ = Nothing
