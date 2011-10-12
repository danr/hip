module Main where

import Prelude (Int,undefined,Eq,Show,Ord,return,div,($),concat)
import qualified Prelude as P

import Language.TPTP
import Language.TPTP.Pretty

nil    = constant "nil"
cons   = binary   "cons"
bottom = constant "bottom"
head   = unary    "head"
tail   = unary    "tail"

infixr 6 ++
(++)   = binary "append"

point    = unary  "point"
reverse  = unary  "reverse"
reverse2 = unary  "reverse2"
revAcc   = binary "revAcc"

diffAxioms :: [Decl]
diffAxioms =
  [ axiom "difflists"  (forall $ \x xs -> cons x xs != nil)
  , axiom "diffbottom" ( nil != bottom 
                       & forall (\x xs -> cons x xs != nil))
  ]

projAxioms :: [Decl]
projAxioms =
  [ axiom "projhead" (forall $ \x xs -> head (cons x xs) === x)
  , axiom "projtail" (forall $ \x xs -> tail (cons x xs) === xs)
  ]

{- 
    (++) :: List -> List -> List
    Cons x xs ++ ys = Cons x (xs ++ ys)
    Nil       ++ ys = ys

    strict in the first argument
-}

isList xs = xs === nil \/ xs === cons (head xs) (tail xs)

appendAxioms :: [Decl]
appendAxioms =
  [ axiom "append_0" (forall $ \x xs ys -> cons x xs ++ ys === cons x (xs ++ ys))
  , axiom "append_1" (forall $      \ys -> nil       ++ ys === ys)
  , axiom "append_2" (forall $ \xs ys -> xs ++ ys === bottom
                                      \/ isList xs)
  ]

{-
    point :: Int -> List
    point x = Cons x Nil
    
    not strict in any argument, never bottom
-}

pointAxioms :: [Decl]
pointAxioms = [ axiom "point_0" (forall $ \x -> point x === cons x nil) ]

{-
    reverse :: List -> List
    reverse (Cons x xs) = reverse xs ++ point x
    reverse Nil         = Nil
-}
    
reverseAxioms :: [Decl]
reverseAxioms =
  [ axiom "reverse_0" (forall $ \x xs -> reverse (cons x xs) === reverse xs ++ point x)
  , axiom "reverse_1" (                  reverse nil === nil)
  , axiom "reverse_2" (forall $   \xs -> reverse xs === bottom
                                      \/ isList xs)
  ]

{-
reverse2 :: List -> List
reverse2 = revAcc Nil
  where 
    revAcc acc Nil         = acc
    revAcc acc (Cons x xs) = revAcc (Cons x acc) xs
-}

reverse2Axioms :: [Decl]
reverse2Axioms =
  [ axiom "reverse2_0" (forall $ \xs -> reverse2 xs === revAcc nil xs)
  , axiom "revAcc_0"   (forall $ \acc      -> revAcc acc nil === acc)
  , axiom "revAcc_1"   (forall $ \acc x xs -> revAcc acc (cons x xs) === revAcc (cons x acc) xs)
  , axiom "revAcc_2"   (forall $ \acc xs   -> revAcc acc xs === bottom
                                           \/ isList xs)
  ]

appendAssoc :: [Decl]
appendAssoc =
  [ conjecture "appendassoc" (forall $ \xs ys zs -> (xs ++ ys) ++ zs === xs ++ (ys ++ zs)) ]

reverseEquivalent :: [Decl]
reverseEquivalent =
  [ conjecture "reveq" (forall $ \xs -> reverse xs === reverse2 xs) ]

main = outputTPTP $ concat [ diffAxioms
                           , projAxioms
                           , appendAxioms
                           , pointAxioms
                           , reverseAxioms 
                           , reverse2Axioms
                           , appendAssoc
                           ]







