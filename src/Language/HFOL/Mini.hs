
data Nat  = Zero | Succ Nat
  deriving (Show,Eq)

data List = Cons Nat List | Nil

plus Zero      n = n
plus (Succ m') n = Succ (plus m' n)

plus' m n = case m of
               Zero -> n
               Succ m' -> plus' m' n

allEq a b c = a == b && b == c
n
main = print (Succ Zero `plus` Succ Zero)