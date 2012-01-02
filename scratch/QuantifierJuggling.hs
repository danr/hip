module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ,(+),pred)

p = predicate "p"
q = predicate "q"


decls :: [Decl]
decls =
  [ conjecture "juggling" $
       (forall' $ \x y -> p y ==> q x)
         <=>
       (exists' p ==> forall' q)
  ]

main :: IO ()
main = outputTPTP decls

