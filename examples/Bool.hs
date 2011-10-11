module Main where

import Test.QuickSpec

bool = describe "Bool" 
                [ var "x" False
                , var "y" False
                , var "z" False
                , con "&&" (&&)
                , con "||" (||)
                , con "not" not
                , con "true" True
                , con "false" False
                ]

main = quickSpec bool True
