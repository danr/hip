data Nat  = Zero | Succ Nat
  deriving (Show,Eq)

{-
foo x | let isZero Zero     = True
            isZero (Succ x) = False
        in  isZero x        = Succ Zero
      | otherwise           = Zero
-}

f x = let z = Succ x in z

g x = let r z = Succ (Succ z) in r x

h x = let r x = Succ (Succ x) in r x