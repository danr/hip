{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Main where

import Prelude (Int,undefined,Eq,Show,Ord,return,div)
import qualified Prelude as P

import Data.Typeable

import Hip.HipSpec
import Test.QuickCheck hiding (Prop)
import Control.Applicative

data ListP a = Cons a (ListP a) | Nil
  deriving (Show,Eq,Ord,Typeable)

(++) :: ListP a -> ListP a -> ListP a
Cons x xs ++ ys = Cons x (xs ++ ys)
Nil       ++ ys = ys

point :: a -> ListP a
point x = Cons x Nil

reverse :: ListP a -> ListP a
reverse (Cons x xs) = reverse xs ++ point x
reverse Nil         = Nil

reverse2 :: ListP a -> ListP a
reverse2 xs = revAcc Nil xs

revAcc :: ListP a -> ListP a -> ListP a
revAcc acc Nil         = acc
revAcc acc (Cons x xs) = revAcc (Cons x acc) xs

type List = ListP Int

prop_revrev :: ListP a -> ListP a -> Prop (ListP a)
prop_revrev xs ys = reverse xs ++ reverse ys =:= reverse (ys ++ xs)

prop_revinv :: ListP a -> Prop (ListP a)
prop_revinv xs = reverse (reverse xs) =:= xs

prop_rev_rev2 :: ListP a -> Prop (ListP a)
prop_rev_rev2 xs = reverse2 xs =:= reverse xs

prop_rev2rev2 :: ListP a -> ListP a -> Prop (ListP a)
prop_rev2rev2 xs ys = reverse2 xs ++ reverse2 ys =:= reverse2 (ys ++ xs)

prop_rev2inv :: ListP a -> Prop (ListP a)
prop_rev2inv xs = reverse2 (reverse2 xs) =:= xs

main = hipSpec "Lists.hs" conf 3
  where conf = describe "Lists"
                [ var "x"        intType
                , var "y"        intType
                , var "z"        intType
                , var "xs"       listType
                , var "ys"       listType
                , var "zs"       listType
                , con "Nil"      (Nil      :: List)
                , con "Cons"     (Cons     :: Int -> List -> List)
                , con "point"    (point    :: Int -> List)
                , con "++"       ((++)     :: List -> List -> List)
                , con "reverse"  (reverse  :: List -> List)
                , con "reverse2" (reverse2 :: List -> List)
                , con "revAcc"   (revAcc   :: List ->  List -> List)
                ]
                   where
                     intType   = undefined :: Int
                     listType  = undefined :: List

instance Arbitrary List where
  arbitrary = sized arbList
    where
      arbList s = frequency [(1,return Nil)
                            ,(s,Cons <$> arbitrary <*> arbList (s `div` 2))
                            ]

instance Classify List where
  type Value List = List
  evaluate = return

-- The tiny Hip Prelude
(=:=) = (=:=)

type Prop a = a
