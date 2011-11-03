import Prelude hiding (even)

data Nat  = Zero | Succ Nat
  deriving (Show,Eq)

plus Zero      n = n
plus (Succ m') n = Succ (plus m' n)

allEq a b c = a == b && b == c

swap (a,b) = (b,a)

main = print (Succ Zero `plus` Succ Zero)
