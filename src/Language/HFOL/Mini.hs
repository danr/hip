
data Nat  = Zero | Succ Nat

data List = Cons Nat List | Nil

plus Zero     n = n
plus (Succ m) n = Succ (plus m n)

plus' m n = case m of
               Zero -> n
               Succ m -> plus' m n
