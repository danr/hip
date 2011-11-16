module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ)

zero = constant "zero"
succ = unary    "succ"

n = constant "n"

primZero = constant "primzero"
primSucc = unary    "primsucc"

primNat = predicate "primnat"

p = predicate "p"

ih = relation "ih"
is = relation "is"
ip = relation "ip"

decls :: [Decl]
decls =
  [ axiom "ihstart" $ p zero ==> ih (primSucc primZero) zero
  , axiom "ihstep"  $ forall' $ \m k -> ih k m & p (succ m)
                                    ==> ih (primSucc k) (succ m)

  , axiom "isstart" $ forall' $ \n' -> is primZero n'
  , axiom "isstep"  $ forall' $ \n' k -> is k (succ n') & p n' ==> is (primSucc k) n'

  , axiom "ipstart" $ forall' $ \n' -> p n' ==> ip primZero n'
  , axiom "ipstep"  $ forall' $ \n' k  -> ip k (succ n') ==> ip (primSucc k) n'

  , question "istest" $ exists' $ \k m -> ih (primSucc k) m & (is k n ==> ip k n)

  , axiom "pz"  $ p zero
  , axiom "psz" $ p (succ zero)
  , axiom "psz" $ p (succ (succ zero))
  , axiom "ih1" $ p n
  , axiom "ih2" $ p (succ n)
  , axiom "ind" $ p (succ (succ n))
  ]

main :: IO ()
main = outputTPTP decls

