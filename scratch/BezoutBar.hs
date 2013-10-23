module Main where

import Language.TPTP.Monad hiding (neg)
import Language.TPTP.Pretty

import Prelude hiding (succ,(+),pred,(*),gcd)

zero = constant "zero"
one  = constant "one"
(+)  = binary   "plus"
(*)  = binary   "mul"
neg  = unary    "neg"
gcd  = binary   "gcd"

divides = relation "divides"

{-
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
-}

commutative' (~~) (#) x y = (x # y) ~~ (y # x)
commutative = commutative' (===)

associative' (~~) (#) x y z = (x # (y # z)) ~~ ((x # y) # z)
associative = associative' (===)

associates = (\ a b -> a `divides` b /\ b `divides` a)

identity (#) c x = x # c === x
isZero (#) c x = x # c === c

ax = axiom "x"

decls :: [Decl]
decls =
    -- Commutative ring axioms
    [ ax $ forall' $ commutative (+)
    , ax $ forall' $ commutative (*)
    , ax $ forall' $ associative (+)
    , ax $ forall' $ associative (*)
    , ax $ forall' $ \ x y z -> x * (y + z) === (x * y) + (x * z)
    , ax $ forall' $ identity (+) zero
    , ax $ forall' $ identity (*) one
    , ax $ forall' $ \ x -> x + neg x === zero
--    , ax $ forall' $ isZero (*) zero
--    -- follows from the other

    -- Integral domain
    , ax $ forall' $ \ x y -> x * y === zero ==> (x === zero \/ y === zero)

    -- Division ring
    , ax $ forall' $ \ a b -> a `divides` b <=> (exists' $ \ x -> b === x * a)
    -- axioms?

    -- GCD ring
    , ax $ forall' $ \ a b c -> c `divides` gcd a b <=> c `divides` a /\ c `divides` b

    -- ok:
    -- , conjecture "x" $ forall' $ \ x -> x `divides` x
    -- ok:
    -- , conjecture "x" $ forall' $ \ x y z -> x `divides` y /\ y `divides` z ==> x `divides` z
    -- ok:
    -- , conjecture "x" $ forall' $ \ a b c -> a `divides` b /\ a `divides` c ==> a `divides` (b + c)
    -- counterexample found, ok:
    -- , conjecture "x" $ forall' $ \ a b -> a `divides` b ==> b `divides` a

    -- ok:
    -- , conjecture "x" $ forall' $ associative' associates gcd
    -- ok:
    -- , conjecture "x" $ forall' $ commutative' associates gcd
    ]

main :: IO ()
main = outputTPTP decls

