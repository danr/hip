-- Two Definitions of Even are Equivalent
-- Mutal Recursion

import Test.QuickCheck

data Nat = S Nat | Z
  deriving (Eq,Show)

instance Arbitrary Nat where
  arbitrary =
    let nats = iterate S Z
    in sized $ \s -> do
          x <- choose (0,s)
          return (nats !! x)

evenm Z     = True
evenm (S n) = oddm n

oddm Z      = False
oddm (S n)  = evenm n

evenr Z = True
evenr (S Z) = False
evenr (S (S x)) = evenr x

prop_evenEq n = evenm n == evenr n

