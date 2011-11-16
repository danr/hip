module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ,(+))

zero = constant "zero"
succ = unary    "succ"
(+)  = binary   "plus"

n = constant "n"

primZero = constant "primzero"
primSucc = unary    "primsucc"

primNat = predicate "primnat"

p = predicate "p"

ih = relation "ih"
is = relation "is"

d = constant "d"

y = constant "y"
z = constant "z"

-- Something is wrong with IH: can prove succ zero + succ zero === succ zero
-- well without plus definition. Not good. Need fix.

decls :: [Decl]
decls =
  [ axiom "p_right_id"  $ forall' $ \x -> p x <=> (x + x === x)

--    axiom "p_assoc"  $ forall' $ \x -> p x <=> (x + (y + z) === (x + y) + z)
--  , lemma "assoclemma" $ forall' $ \y z -> succ (y + z) === succ y + z

--  , axiom "pluszero" $ forall' $ \y   -> zero          + y === y
--  , axiom "plussucc" $ forall' $ \y   -> succ zero     + y === succ y
--  , axiom "plusstep" $ forall' $ \x y -> succ (succ x) + y === succ (succ (x + y))

{-
  , axiom "pluszero" $ forall' $ \y   -> zero   + y === y
  , axiom "plusstep" $ forall' $ \x y -> succ x + y === succ (x + y)
-}

  , axiom "ihstart" $ forall' $ \x   -> ih primZero x
  , axiom "ihstep"  $ forall' $ \x k -> (ih k (succ x) & p x) <=> ih (primSucc k) x

--  , axiom "isstart" $ forall' $ \n'    -> p n'           ==> is primZero n'
--  , axiom "isstep"  $ forall' $ \n' k  -> is k (succ n') ==> is (primSucc k) n'

--  , conjecture "induction" $ exists' $ \k -> ih k zero & (ih k n ==> is k n)

  , axiom "defined" $  d === primSucc (primZero)
  , conjecture "ind" $ ih d zero -- & (ih d n ==> is d n)

  ]

main :: IO ()
main = outputTPTP decls

