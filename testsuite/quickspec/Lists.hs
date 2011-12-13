{-# LANGUAGE TypeFamilies, DeriveDataTypeable #-}
module Main where

import Prelude (Int,undefined,Eq,Show,Ord,return,div)
import qualified Prelude as P

import Data.Typeable

import Test.QuickSpec
import Test.QuickCheck
import Control.Applicative

data List = Cons Int List | Nil
  deriving (Show,Eq,Ord,Typeable)

(++) :: List -> List -> List
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

point :: Int -> List
point x = Cons x Nil

reverse :: List -> List
reverse (Cons x xs) = reverse xs ++ point x
reverse Nil         = Nil

reverse2 :: List -> List
reverse2 = revAcc Nil

revAcc :: List -> List -> List
revAcc acc Nil         = acc
revAcc acc (Cons x xs) = revAcc (Cons x acc) xs

instance Arbitrary List where
  arbitrary = sized arbList
    where 
      arbList s = frequency [(1,return Nil)
                            ,(s,Cons <$> arbitrary <*> arbList (s `div` 2))
                            ]

instance Classify List where
  type Value List = List
  evaluate = return

lists = describe "Lists"
                [ var "x"  intType
                , var "y"  intType
                , var "z"  intType
                , var "xs" listType
                , var "ys" listType
                , var "zs" listType
                , con "[]"      Nil
                , con ":"       Cons
                , con "point"   point
                , con "++"      (++)
                , con "reverse"  reverse
                , con "reverse2" reverse2
                , con "revAcc"   revAcc
                ]
  where
    intType   = undefined :: Int
    listType  = undefined :: List
    unOpType  = undefined :: Int -> Int
    binOpType = undefined :: Int -> Int -> Int

main = quickSpecDepth lists 3
