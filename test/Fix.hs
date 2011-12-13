{-# LANGUAGE NPlusKPatterns #-}
module Fix where

import Data.Function

data Nat = Zero | Succ Nat

plus = fix plus'

plus' p 0       y = y
plus' p (x + 1) y = p x y + 1