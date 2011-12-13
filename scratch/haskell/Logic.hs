{-# LANGUAGE FlexibleInstances #-}
module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

p = predicate "p"
q = predicate "q"

axioms :: [Decl]
axioms =
  [ axiom "a" (exists p ==> exists q)
  , conjecture "c" (exists $ \x -> p x ==> q x)
  ]

main = outputTPTP axioms

