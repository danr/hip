module AutoPrelude (module Test.QuickCheck,Prop,(=:=),prove) where

import Test.QuickCheck hiding (Prop)

infix 1 =:=

data Prop a = a :=: a

prove x = x

(=:=) = (:=:)

instance Eq a => Testable (Prop a) where
  property (lhs :=: rhs) = property (lhs == rhs)

