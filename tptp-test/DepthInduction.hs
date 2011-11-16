module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ,(+))

zero = constant "zero"
succ = unary    "succ"
(+)  = binary   "plus"

primZero = constant "primzero"
primSucc = unary    "primsucc"

primNat = predicate "primnat"

p = predicate "p"

ih = relation "ih"
is = relation "is"

d = constant "d"

decls :: [Decl]
decls =
  [
--    axiom "p_idem"  $ forall' $ \x -> p x <=> (x + x === x)
    axiom "p_assoc"  $ forall' $ \x -> p x <=> (forall' $ \y z -> x + (y + z) === (x + y) + z)
  , lemma "assoclemma" $ forall' $ \y z -> succ (y + z) === succ y + z
--    axiom "p_r_id" $ forall' $ \x -> p x <=> (x + zero === x)
--    axiom "p_movesuc" $ forall' $ \x -> p x <=> (forall' $ \y -> succ x + y === x + succ y)

  , axiom "pluszero" $ forall' $ \y   -> zero          + y === y
  , axiom "plussucc" $ forall' $ \y   -> succ zero     + y === succ y
  , axiom "plusstep" $ forall' $ \x y -> succ (succ x) + y === succ (succ (x + y))

--  , axiom "pluszero" $ forall' $ \y   -> zero   + y === y
--  , axiom "plusstep" $ forall' $ \x y -> succ x + y === succ (x + y)

  , axiom "ihstart"  $ forall' $ \x   -> ih primZero x
  , axiom "ihstep"   $ forall' $ \x k -> (ih k (succ x) & p x) <=> ih (primSucc k) x

  , axiom "isstart"  $ forall' $ \n   -> p n           ==> is primZero n
  , axiom "isstep"   $ forall' $ \n k -> is k (succ n) ==> is (primSucc k) n

  , question "induction" $
        exists' $ \k -> forall' $ \n -> ih k zero & (ih k n ==> is k n)

  ]

main :: IO ()
main = outputTPTP decls

