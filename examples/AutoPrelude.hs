module AutoPrelude (module Test.QuickCheck
                   ,Prop,(=:=),(=/=),prove,proveBool) where

import Test.QuickCheck hiding (Prop)

infix 1 =:=

data Prop a = a :=: a | a :/: a

prove x = x

proveBool lhs = lhs =:= True

(=:=) = (:=:)
(=/=) = (:/:)

instance Eq a => Testable (Prop a) where
  property (lhs :=: rhs) = property (lhs == rhs)
  property (lhs :/: rhs) = expectFailure (lhs == rhs)

