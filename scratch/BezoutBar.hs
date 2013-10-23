module Main where

import Language.TPTP.Monad hiding (neg)
import qualified Language.TPTP.Monad as L
import Language.TPTP.Pretty

import Prelude hiding (succ,(+),pred,(*),gcd)

zero = constant "zero"
one  = constant "one"
(+)  = binary   "plus"
(*)  = binary   "mul"
neg  = unary    "neg"
gcd  = binary   "gcd"

infixl 5 +
infixl 6 *
infix 4 %=

(%|) = relation "divides"

commutative' (~~) (#) x y = (x # y) ~~ (y # x)
commutative = commutative' (===)

associative' (~~) (#) x y z = (x # (y # z)) ~~ ((x # y) # z)
associative = associative' (===)

-- associates:
(%=) = (\ a b -> a %| b /\ b %| a)

identity (#) c x = x # c === x
isZero (#) c x = x # c === c

ax = axiom "x"
conj = conjecture "x"

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
    , ax $ forall' $ \ x -> x + (neg x) === zero
    , ax $ forall' $ isZero (*) zero
--    -- follows from the other

    -- Integral domain
    , ax $ forall' $ \ x y -> x * y === zero ==> (x === zero \/ y === zero)

    -- Division ring
    , ax $ forall' $ \ a b -> a %| b <=> (exists' $ \ x -> b === x * a)
    -- ok:
    -- , conj $ forall' $ \ a b -> L.neg (a %| b) <=> (forall' $ \ x -> b != x * a)

    -- GCD ring
    , ax $ forall' $ \ a b c -> c %| gcd a b <=> c %| a /\ c %| b

    -- ok:
    , ax $ forall' $ \ x -> x %| x
    -- ok:
    , ax $ forall' $ \ x y z -> x %| y /\ y %| z ==> x %| z
    -- ok:
    , ax $ forall' $ \ a b c -> a %| b /\ a %| c ==> a %| (b + c)
    -- counterexample found, ok:
--   , ax $ forall' $ \ a b -> a %| b ==> b %| a

    -- ok:
    , ax $ forall' $ associative' (%=) gcd
    -- ok:
    , ax $ forall' $ commutative' (%=) gcd

    -- Bézout ring
    , ax $ forall' $ \ a b -> exists' $ \ x y -> a * x + b * y %= gcd a b

-- Lorenzini:
    , conj $ forall' $ \ a b c ->
         (exists' $ \ x y z -> a * x + b * y + c * z %= one) ==>
         (exists' $ \ p q x' y' -> p * a * x' + (p * b + q * c) * y' %= one)

-- Lombardi:
{-
    , conj $ forall' $ \ a b c ->
        (exists' $ \ x y z -> a * x + b * y + c * z %= one) ==>
        (exists' $ \ p q x' y' -> p * x' * a + q * x' * b + q * y' * c %= one)
-}
    ]

main :: IO ()
main = outputTPTP decls

