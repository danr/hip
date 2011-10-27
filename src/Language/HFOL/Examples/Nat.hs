module Main where

import Prelude hiding (succ,(+),(==))

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Language.HFOL.Parser
import Language.HFOL.ToTPTP

zero   = constant "Zero"
succ   = unary "Succ"
(+)    = binary "plus"
(==)   = binary "eq"
approx = binary "approx"

n = constant "n"

plusassoc =
  [ axiom "IH"      $ forall $ \x y z -> approx n        (x + (y + z)) === approx n        ((x + y) + z)
  , conjecture "IS" $ forall $ \x y z -> approx (succ n) (succ x + (y + z)) === approx (succ n) ((succ x + y) + z)
  ]



rightident =
  [ axiom "IH"      $ forall $ \x -> approx n        (x + zero)      === approx n        x
  , conjecture "IS" $ forall $ \x -> approx (succ n) (succ x + zero) === approx (succ n) (succ x)
  ]



-- Luckily, this is unprovable!
idempotent =
  [ axiom "IH"      $ forall $ \x -> approx n        (x + x)           === approx n        x
  , conjecture "IS" $ forall $ \x -> approx (succ n) (succ x + succ x) === approx (succ n) (succ x)
  ]



movesuc =
  [ axiom "IH"      $ forall $ \x y -> approx n        (succ x + y)        === approx n        (x + succ y)
  , conjecture "IS" $ forall $ \x y -> approx (succ n) (succ (succ x) + y) === approx (succ n) (succ x + succ y)
  ]


-- Commutativivity needs the move-suc lemma!
commutative =
  [ axiom "movesuc" $ forall $ \m x y -> approx m        (succ x + y) === approx m        (x + succ y)
  , axiom "IH"      $ forall $ \x y   -> approx n        (x + y)      === approx n        (y + x)
  , conjecture "IS" $ forall $ \x y   -> approx (succ n) (succ x + y) === approx (succ n) (y + succ x)
  ]

-- No luck without approx :(
commutativeApproxless =
  [ axiom "movesuc" $ forall $ \x   -> (succ x + zero) === (zero + succ x)
  , axiom "IB"      $ forall $ \b -> (zero + b)      === (b + zero)
  , axiom "IH"      $ forall $ \a b -> (a + b)         === (a + b)
  , conjecture "IS" $ forall $ \a b -> (succ a + b)    === (a + succ b)
  ]

main = do
  printAxiomsFromFile "nat.ec"
  outputTPTP commutativeApproxless

printAxiomsFromFile :: String -> IO ()
printAxiomsFromFile file = do
  ds <- parseFile file
  let (funcAxiomsWithDef,extraAxioms,_) = toTPTP ds
      axioms = concatMap snd funcAxiomsWithDef ++ extraAxioms
  putStrLn (prettyTPTP axioms)

