
data Nat = Succ Nat | Zero
data Bool = True | False

even n = let even (Succ x) = not (odd x)
             even Zero     = True
             odd (Succ x)  = not (even x)
             odd Zero      = True
         in even n
  where
             not True      = False
             not False     = True

