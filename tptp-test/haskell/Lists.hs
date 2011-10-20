{-# LANGUAGE FlexibleInstances #-}
module Main where

import Prelude (Int,undefined,Eq,Show,Ord,return
               ,div,($),concat,(.),map,String,(>>=))
import qualified Prelude as P

import Language.TPTP.Monad
import Language.TPTP.Pretty

nil    = constant "nil"
cons   = binary   "cons"
bottom = constant "bottom"
head   = unary    "head"
tail   = unary    "tail"

infixr 6 `cons`

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
                       & forall (\x xs -> cons x xs != bottom))
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

[a,b,c] = map (constant . return) "abc"

tests :: [Decl]
tests =
  [ conjecture "tests" $ (a `cons` b `cons` nil ++ point c === a `cons` b `cons` c `cons` nil)
                       & (reverse (a `cons` b `cons` c `cons` nil) === c `cons` b `cons` a `cons` nil)
                       & (a `cons` b `cons` point c === reverse2 (c `cons` b `cons` point a))
  ]

infixl 9 @@
(@@)   = binary "app"
approx = binary "approx"

approxDefn :: [Decl]
approxDefn =
  [ axiom "approx_0" (forall $ \h      -> approx h nil === nil)
  , axiom "approx_1" (forall $ \h x xs -> approx h (cons x xs) === cons x (h @@ xs))
  , axiom "approx_2" (forall $ \h xs   -> approx h xs === bottom
                                       \/ isList xs)
  ]

h = constant "h"

class EqualityBuilder t where
  eqConj'
      :: String
      -> [VarName]
      -> t
      -> M [Decl]

instance EqualityBuilder (M Term,M Term) where
  eqConj' name vars (lhs,rhs) = do
    ih <- h @@ lhs === h @@ rhs
    is <- approx h lhs === approx h rhs
    return [ Axiom      (concat [name,"IH"]) (Forall (P.reverse vars) ih)
           , Conjecture (concat [name,"IS"]) (Forall (P.reverse vars) is)
           ]

instance EqualityBuilder r => EqualityBuilder (M Term -> r) where
  eqConj' name vars f = newVar >>= \v -> eqConj' name (v:vars) (f (return (Var v)))

eqConj name = run . eqConj' name []

assocConj :: [Decl]
assocConj = eqConj "appendAssoc" $ \xs ys zs -> ((xs ++ ys) ++ zs , xs ++ (ys ++ zs))

leftIdConj :: [Decl]
leftIdConj = eqConj "leftId" $ \xs -> (xs ++ nil,xs)

appendAssocLemma :: [Decl]
appendAssocLemma = [ axiom "appendAssocLemma" (forall $ \xs ys zs -> (xs ++ ys) ++ zs === xs ++ (ys ++ zs)) ]

leftIdLemma :: [Decl]
leftIdLemma = [ axiom "leftIdLemma" (forall $ \xs -> xs ++ nil === xs) ]

{-
  This is not true in a setting with bottoms.

  reverse (1 : undefined ++ [ 1 ]) !=
  1 : reverse (1 : undefined)
-}

revStepConj :: [Decl]
revStepConj = eqConj "revStepEq" $ \x xs -> (reverse (xs ++ point x),x `cons` reverse xs)

rev2StepConj :: [Decl]
rev2StepConj = eqConj "rev2StepEq" $ \x xs -> (reverse2 (x `cons` xs),reverse2 xs ++ point x)

revEqConj :: [Decl]
revEqConj = eqConj "revEq" $ \xs -> (reverse xs,reverse2 xs)

revRevStepConj :: [Decl]
revRevStepConj = eqConj "revRevStepEq" $ \x xs -> (reverse (reverse (x `cons` xs)),x `cons` reverse (reverse xs))

revRevConj :: [Decl]
revRevConj = eqConj "revRevEq" $ \xs -> (reverse (reverse xs),xs)

revAppConj :: [Decl]
revAppConj = eqConj "revAppEq" $ \xs ys -> (reverse2 (xs ++ ys),reverse2 ys ++ reverse2 xs)

revAccConj :: [Decl]
revAccConj = eqConj "revAccEq" $ \xs ys -> (revAcc ys xs,reverse2 xs ++ ys)

main = outputTPTP $ concat [ diffAxioms
                           , projAxioms
                           , appendAxioms
                           , pointAxioms
                           , reverseAxioms
                           , reverse2Axioms
                           , appendAssocLemma
                           , leftIdLemma
                           , approxDefn
--                           , revStepLemma
                           , revStepConj
--                           , assocConj
--                           , leftIdConj
                           ]







