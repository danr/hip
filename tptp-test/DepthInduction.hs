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

decls :: [Decl]
decls =
  [ axiom "p_r_id"   $ forall' $ \x   -> p x <=> (x + zero === x)


  , axiom "pluszero" $ forall' $ \y   -> zero          + y === y
  , axiom "plussucc" $ forall' $ \y   -> succ zero     + y === succ y
  , axiom "plusstep" $ forall' $ \x y -> succ (succ x) + y === succ (succ (x + y))


{-
  , axiom "pluszero" $ forall' $ \y   -> zero   + y === y
  , axiom "plusstep" $ forall' $ \x y -> succ x + y === succ (x + y)
  -}

  , axiom "ihstart" $ forall' $ \x   -> p x <=> ih primZero x
  , axiom "ihstep"  $ forall' $ \x k -> (ih k (succ x) & p x) <=> ih (primSucc k) x

  , axiom "isstart" $ forall' $ \n'    -> p (succ n')    ==> is primZero n'
  , axiom "isstep"  $ forall' $ \n' k  -> is k (succ n') ==> is (primSucc k) n'

  , question "induction" $ exists' $ \k -> ih k zero & (ih k n ==> is k n)

--  , question "testbasecases" $ exists' $ \k -> ih k zero



{-  , axiom "pz"  $ p zero
  , axiom "psz" $ p (succ zero)
  , axiom "psz" $ p (succ (succ zero))
  , axiom "ih1" $ p n
  , axiom "ih2" $ p (succ n)
  , axiom "ind" $ p (succ (succ n))
  -}
  ]

main :: IO ()
main = outputTPTP decls

