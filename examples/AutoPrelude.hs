{-# LANGUAGE OverlappingInstances, FlexibleInstances #-}
module AutoPrelude (module Test.QuickCheck
                   ,Prop,(=:=),(=/=),prove,proveBool) where

import Test.QuickCheck hiding (Prop)

infix 1 =:=

data Prop a = a :=: a | a :/: a

-- default (Int)

prove x = x

proveBool lhs = lhs =:= True

(=:=) = (:=:)
(=/=) = (:/:)

instance Eq a => Testable (Prop a) where
  property (lhs :=: rhs) = property (lhs == rhs)
  property (lhs :/: rhs) = expectFailure (lhs == rhs)

-- Needed for infinite examples
instance Eq a => Testable (Prop [a]) where
  property (lhs :=: rhs) = property (take 10 lhs == take 10 rhs)
  property (lhs :/: rhs) = expectFailure (take 10 lhs == take 10 rhs)

instance Show (a -> b) where
  show _ = "<fun>"
