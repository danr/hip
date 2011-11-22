module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ,(+),pred)

zero = constant "zero"
succ = unary    "succ"
pred = unary    "pred"
(+)  = binary   "plus"

primZero = constant "primzero"
primSucc = unary    "primsucc"

primNat = predicate "primnat"

p = predicate "p"

ih = trinaryRel "ih"
-- is = binary "is"

($$)    = binary "app"
succPtr = constant "succptr"
predPtr = constant "predptr"

d = constant "d"

decls :: [Decl]
decls =
  [ axiom "predsucc" $ forall' $ \n -> succ (pred n) === n
  , axiom "predptr"  $ forall' $ \n -> predPtr $$ n === pred n
  , axiom "succptr"  $ forall' $ \n -> succPtr $$ n === succ n

--  , axiom "pluszero" $ forall' $ \y   -> zero          + y === y
--  , axiom "plussucc" $ forall' $ \y   -> succ zero     + y === succ y
--  , axiom "plusstep" $ forall' $ \x y -> succ (succ x) + y === succ (succ (x + y))

  , axiom "pluszero" $ forall' $ \y   -> zero   + y === y
  , axiom "plusstep" $ forall' $ \x y -> succ x + y === succ (x + y)



  -- ih f k x == foldr (&&) True (take k (iterate f x))
  , axiom "ihstart"  $ forall' $ \f x   -> ih f primZero x
  , axiom "ihstep"   $ forall' $ \f x k -> (ih f k (f $$ x) & p x)
                                       <=> ih f (primSucc k) x

--  , axiom "isstart"  $ forall' $ \n   -> p n           ==> is primZero n
--  , axiom "isstep"   $ forall' $ \n k -> is k (succ n) ==> is (primSucc k) n

--  , question "induction" $
--        exists' $ \k -> forall' $ \n -> ih succPtr k zero
--                                     & (ih predPtr k (pred n) ==> p n)

  , conjecture "testbase" $
        forall' $ \n -> ih predPtr (primSucc primZero) (pred n) ==> p n

--  , axiom "p_all_zero" $ forall' $ \x -> p x <=> (x === zero)
--  ,  axiom "p_idem"  $ forall' $ \x -> p x <=> (x + x === x)

--  , axiom "p_assoc"  $ forall' $ \x -> p x <=>
--                      (forall' $ \y z -> x + (y + z) === (x + y) + z)
--  , lemma "assoclemma" $ forall' $ \y z -> succ (y + z) === succ y + z
--  , axiom "p_r_id" $ forall' $ \x -> p x <=> (x + zero === x)
--    axiom "p_movesuc" $ forall' $ \x -> p x <=>
--                         (forall' $ \y -> succ x + y === x + succ y)


  ]

main :: IO ()
main = outputTPTP decls

