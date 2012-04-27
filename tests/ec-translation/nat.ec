data Nat = Succ Nat | Zero;
data T a b = T a b;

eq n m = case T n m of
           { T Zero     Zero     -> True
           ; T (Succ n) (Succ m) -> eq n m
           ; _                   -> False
           };

plus n m = case n of
             { Zero -> m
             ; Succ n -> Succ (plus n m)
             };

approx n x = case T n x of
             { T (Succ n) Zero     -> Zero
             ; T (Succ n) (Succ x) -> Succ (approx n x)
             };
