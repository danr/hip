module Main where

import Prelude hiding (take,pred,head,tail)

import Language.TPTP
import Language.TPTP.Pretty

{-

-- The definition
take Zero    xs          = Nil
take (Suc n) (Cons x xs) = Cons x (take n xs)
take (Suc n) Nil         = Nil

-- desugared to
take' n xs = case n of
  Zero  -> Nil
  Suc n -> takeSuc n xs
  _     -> ⊥

takeSuc n xs = case xs of
  Cons x xs -> Cons x (take' n xs)
  Nil       -> Nil
  _         -> ⊥

-- interpreted as
take' Zero    xs = Nil
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

diffAxioms :: [Decl]
diffAxioms =
  [ axiom "diffnats"   (forall $ \n    -> suc n     != zero)

  , axiom "difflists"  (forall $ \x xs -> cons x xs != nil)

  , axiom "diffbottom" ( zero != bottom & nil != bottom 

                       & forall (\n -> suc n != nil)

                       & forall (\x xs -> cons x xs != nil))
  ]

projAxioms :: [Decl]
projAxioms =
  [ axiom "projpred" (forall $ \n    -> pred (suc n) === n)

  , axiom "projhead" (forall $ \x xs -> head (cons x xs) === x)

  , axiom "projtail" (forall $ \x xs -> tail (cons x xs) === xs)
  ]

takeAxioms :: [Decl]
takeAxioms =
  [ axiom "take0" (forall $ \xs -> take zero xs === nil)

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

one   = suc zero
two   = suc one
three = suc two

infixr 5 `cons`

takeTest :: Decl
takeTest = conjecture "takeTest" $
       take two (three `cons` one `cons` two `cons` three `cons` one `cons` nil)
   ===          (three `cons` one `cons` nil)

main = outputTPTP (diffAxioms ++ projAxioms ++ takeAxioms ++ [takeTest])



