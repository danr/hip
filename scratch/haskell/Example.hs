{-# LANGUAGE OverloadedStrings #-}
module Example where

import Codec.TPTP

x = V "X"
y = V "Y"

p = AtomicWord "p"
q = AtomicWord "q"

-- Modus ponens but with predicates p,q and quantification

modusPonens0 :: Formula
modusPonens0 = for_all [x] $ pApp p [var x] .=>. pApp q [var x]

modusPonens1 :: Formula
modusPonens1 = exists [x] $ pApp p [var x]

modusPonens2 :: Formula
modusPonens2 = exists [x] $ pApp q [var x]

modusPonens :: [TPTP_Input]
modusPonens = [ AFormula "modusPonens0" (Role "axiom") modusPonens0 NoAnnotations
              , AFormula "modusPonens1" (Role "axiom") modusPonens1 NoAnnotations
              , AFormula "modusPonens2" (Role "conjecture") modusPonens2 NoAnnotations
              ]
              
mkMPfile = writeFile "modus_ponens.tptp" (toTPTP' modusPonens)