module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ)

zero = constant "zero"
succ = unary    "succ"

n = constant "n"

primZero = constant "primzero"
primSucc = unary    "primsucc"

p = predicate "p"

ih = relation "ih"
is = relation "is"

decls :: [Decl]
decls =
  [ axiom "ihstart" $ p zero ==> ih primZero zero
  , axiom "ihstep"  $ forall' $ \m k -> ih k m & p (succ m)
                                    ==> ih (primSucc k) (succ m)
  , axiom "isstart" $ forall' $ \n' -> (p n' ==> p (succ n'))
                                   ==> is primZero n'
  , axiom "isstep"  $ forall' $ \n' k -> (p n' ==> is k (succ n'))
                                     ==> is (primSucc k) n'
  , question "ind"  $ exists' $ \k m -> ih k m & is k n

  , axiom "pz" $ p zero
  , axiom "psz" $ p (succ zero)
--  , axiom "psz" $ p (succ (succ zero))
  , axiom "ind" $ forall' $ \m -> p m ==> p (succ (succ (succ m)))
  ]

main :: IO ()
main = outputTPTP decls

