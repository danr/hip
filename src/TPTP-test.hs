module Main where

import Prelude hiding (take,pred,head,tail)

import Language.TPTP
import Language.TPTP.Pretty

{-

-- The definition
take Zero    xs          = xs
take (Suc n) (Cons x xs) = Cons x (take n xs)
take (Suc n) Nil         = Nil

-- desugared to
take' n xs = case n of
  Zero  -> xs
  Suc n -> takeSuc n xs
  _     -> ⊥

takeSuc n xs = case xs of
  Cons x xs -> Cons x (take' n xs)
  Nil       -> Nil
  _         -> ⊥

-- interpreted as
take' Zero    xs = xs
take' (Suc n) xs = takeSuc n xs
take' _       xs = ⊥

takeSuc n (Cons x xs) = Cons x (take' n xs)
takeSuc n Nil         = Nil
takeSuc n _           = ⊥

-}

-- Definitions
suc  = unary    "suc"
pred = unary    "pred"
zero = constant "zero"
nil  = constant "nil"
cons = binary   "cons"
head = unary    "head"
tail = unary    "tail"

bottom = constant "bottom"

take    = binary "take"
takeSuc = binary "takeSuc"

take_axioms =
  [ axiom "take0" (forall $ \xs -> take zero xs === xs)

  , axiom "take1" (forall $ \n xs -> take (suc n) xs === takeSuc n xs)

  , axiom "take2" (forall $ \n xs -> take n xs === bottom
                                  \/ n === zero
                                  \/ n === suc (pred n))

  , axiom "take3" (forall $ \n x xs -> takeSuc n (cons x xs) === cons x (take n xs))

  , axiom "take4" (forall $ \n -> takeSuc n nil === nil)

  , axiom "take5" (forall $ \n xs -> takeSuc n xs === bottom
                                  \/ xs === cons (head xs) (tail xs)
                                  \/ xs === nil)
  ]

printAxioms = putStr (unlines (map pretty take_axioms))



