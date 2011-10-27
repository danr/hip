module Main where

import Prelude hiding (succ,(+),(==),(.),map,iterate)

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Language.HFOL.Parser
import Language.HFOL.ToTPTP

zero    = constant "Zero"
succ    = unary "Succ"
(+)     = binary "plus"
(==)    = binary "eq"
approx  = binary "approx"
map     = binary "map"
iterate = binary "iterate"
(.)     = binary "compose"
($$)    = binary "app"
bimap   = trinary "bimap"
bimap2  = trinary "bimap2"
cons    = binary "Cons"

n = constant "n"

-- Map-iterate property
mapiterate =
  [ axiom "IH"      $ forall $ \f x -> approx n        (map f (iterate f x)) === approx n        (iterate f (f $$ x))
  , conjecture "IS" $ forall $ \f x -> approx (succ n) (map f (iterate f x)) === approx (succ n) (iterate f (f $$ x))
-- Which one to use? Both are provable! :(
--  , conjecture "IS" $ forall $ \f x -> approx (succ n) (map f (iterate f (f $$ x))) === approx (succ n) (iterate f (f $$ (f $$ x)))
  ]

mapcomp =
  [ axiom "IH"      $ forall $ \f g xs -> approx n        (map f (map g xs)) === approx n        (map (f . g) xs)
  , conjecture "IS" $ forall $ \f g xs -> approx (succ n) (map f (map g xs)) === approx (succ n) (map (f . g) xs)
  ]

bimaps =
  [ axiom "IH"      $ forall $ \f g xs   -> approx n        (bimap f g xs)          === approx n        (bimap2 f g xs)
  , conjecture "IS" $ forall $ \f g x xs -> approx (succ n) (bimap f g (cons x xs)) === approx (succ n) (bimap2 f g (cons x xs))
  ]

main = do
  printAxiomsFromFile "listfun.ec"
  outputTPTP bimaps

printAxiomsFromFile :: String -> IO ()
printAxiomsFromFile file = do
  ds <- parseFile file
  let (funcAxiomsWithDef,extraAxioms,_) = toTPTP ds
      axioms = concatMap snd funcAxiomsWithDef ++ extraAxioms
  putStrLn (prettyTPTP axioms)

