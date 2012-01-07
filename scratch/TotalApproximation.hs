module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ,(+),pred,id)

zero = constant "zero"
suc  = unary    "suc"
pred = unary    "pred"
(+)  = binary   "plus"

bottom = constant "bot"

total = predicate "total"

id = unary "id"
un = unary "un"

(<==) = flip (==>)

decls :: [Decl]
decls =
  [ axiom "predsuc" $ forall' $ \n -> pred (suc n) === n

  , axiom "disjsuczero" $ forall' $ \n -> suc n != zero
  , axiom "disjsucbot"  $ forall' $ \n -> suc n != bottom
  , axiom "disjzerobot" $                 zero  != bottom

  , axiom "totalzero"   $                                          total zero
  , axiom "totalsuc"    $ forall' $ \n   -> total n            <=> total (suc n)
  , axiom "totalplus"   $ forall' $ \x y -> total x /\ total y ==> total (x + y)
  , axiom "totalplusrv" $ forall' $ \x y -> total x            <== total (x + y)
  , axiom "totalid"     $ forall' $ \x   -> total x            <=> total (id x)
  , axiom "totalun"     $ forall' $ \x   -> total x            <=> total (un x)
  , axiom "nottotalbot" $ neg (total bottom)

  , axiom "pluszero" $ forall' $   \y -> zero  + y === y
  , axiom "plusstep" $ forall' $ \x y -> suc x + y === suc (x + y)
  , axiom "plusbot"  $ forall' $ \x y -> x     + y === bottom \/ x === zero \/ x === suc (pred x)

  , axiom "idzero" $                 id zero    === zero
  , axiom "idsuc"  $ forall' $ \x -> id (suc x) === suc (un x)
  , axiom "idbot"  $ forall' $ \x -> id x       === bottom \/ x === zero \/ x === suc (pred x)

-- Works :)
--  , axiom "hyp"       $ forall' $ \x -> total x ==> un (zero + x) === un x
--  , conjecture "conc" $ forall' $ \x -> total x ==> id (zero + x) === id x

-- Works
--  , axiom "hyp"       $ forall' $ \x -> total x ==> un (x + zero) === un x
--  , conjecture "conc" $ forall' $ \x -> total x ==> id (x + zero) === id x

-- Timeout
--  , axiom "hyp"       $ forall' $ \x y -> total x /\ total y ==> un (x + y) === un (y + x)
--  , conjecture "conc" $ forall' $ \x y -> total x /\ total y ==> id (x + y) === id (y + x)

-- Timeout :)
--  , axiom "hyp"       $ forall' $ \x -> total x ==> un x === un (x + x)
--  , conjecture "conc" $ forall' $ \x -> total x ==> id x === id (x + x)

-- Timeout
--  , axiom "hyp"       $ forall' $ \x y -> total x /\ total y ==> un (suc x + y) === un (x + suc y)
--  , conjecture "conc" $ forall' $ \x y -> total x /\ total y ==> id (suc x + y) === id (x + suc y)

-- Works
  , axiom "hyp"       $ forall' $ \x y z -> total x /\ total y /\ total z ==> un (x + (y + z)) === un ((x + y) + z)
  , conjecture "conc" $ forall' $ \x y z -> total x /\ total y /\ total z ==> id (x + (y + z)) === id ((x + y) + z)
  ]

main :: IO ()
main = outputTPTP decls

