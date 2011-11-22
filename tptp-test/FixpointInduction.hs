module Main where

import Language.TPTP.Monad
import Language.TPTP.Pretty

import Prelude hiding (succ,(+),pred)

zero    = constant "zero"
succ    = unary    "succ"
bottom  = constant "bottom"
plus    = trinary  "plus"
plusPtr = constant "plusptr"
r       = constant "r"
pred    = unary    "pred"

infixl 6 $$
($$)   = binary   "app"

p      = predicate "p"

decls :: [Decl]
decls =
  [ axiom "pluszero"  $ forall' $ \r y   -> plus r zero     y === y
  , axiom "plusstep"  $ forall' $ \r x y -> plus r (succ x) y === succ (r $$ x $$ y)
  , axiom "pluscases" $ forall' $ \r x y -> plus r x        y === bottom
                                         \/ x === succ (pred x)
                                         \/ x === zero

  , axiom "predsucc"  $ forall' $ \n -> pred (succ n) === n
  , axiom "diffsz"    $ forall' $ \n -> succ n != zero
  , axiom "diffsb"    $ forall' $ \n -> succ n != bottom
  , axiom "diffzb"    $                 bottom != zero
  , axiom "appbottom" $ forall' $ \x     -> bottom $$ x === bottom
  , axiom "appplus"   $ forall' $ \r x y -> plusPtr $$ r $$ x $$ y === plus r x y

  , axiom "assoc" $ forall' $ \f -> p f
--                         <=> forall' (\x -> x === f $$ zero $$ x)
                           <=> forall' (\x y z -> let x' * y' = f $$ x' $$ y'
                                                  in  x * (y * z) === (x * y) * z)

--  , conjecture "fixbase" $ forall' $ \f -> p f ==> p (plusPtr $$ f)
  , axiom "ih" $ p r
  , conjecture "is" $ p (plusPtr $$ r)
  ]

main :: IO ()
main = outputTPTP decls

