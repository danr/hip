
data Nat  = Zero | Succ Nat

data Bool = True | False

plus Zero      n = n
plus (Succ m') n = Succ (plus m' n)

Zero == Zero = True
Succ n == Succ m = n == m
_ == _ = False

True && b = b
_    && _ = False

allEq a b c = a == b && b == c

swap (a,b) = (b,a)

print = print

main = print (Succ Zero `plus` Succ Zero)
