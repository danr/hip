module BoolLists where

import AutoPrelude
import Prelude (Bool(..),undefined)

otherwise = True

True  == True  = True
False == False = True
_     == _     = False

nub :: [Bool] -> [Bool]
nub (True :True :xs) = nub (True:xs)
nub (False:False:xs) = nub (False:xs)
nub (x:xs)           = x:nub xs
nub _                = []

nub' :: [Bool] -> [Bool]
nub' (x:y:xs) | x == y    = nub' (y:xs)
              | otherwise = x:nub' (y:xs)
nub' xs                   = xs

prop_nub_idem :: [Bool] -> Prop [Bool]
prop_nub_idem xs = nub (nub xs) =:= nub xs

prop_nub'_idem :: [Bool] -> Prop [Bool]
prop_nub'_idem xs = nub' (nub' xs) =:= nub' xs

prop_nub_equal :: Prop ([Bool] -> [Bool])
prop_nub_equal = nub =:= nub'

