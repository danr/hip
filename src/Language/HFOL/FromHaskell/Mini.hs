
data Nat  = Zero | Succ Nat
  deriving (Show,Eq)

data List = Cons Nat List | Nil

{-
plus Zero      n = n
plus (Succ m') n = Succ (plus m' n)
-}

{-
plus' m n = case m of
               Zero -> n
               Succ m' -> plus' m' n
-}

{-
allEq a b c = a == b && b == c

swap (a,b) = (b,a)

main = print (Succ Zero `plus` Succ Zero)

foo x | let isZero Zero     = True
            isZero (Succ x) = False
        in  isZero x               = Succ Zero
      | otherwise                  = Zero
-}

{-

data K = A | B | C

even (Succ (Succ n)) = even n
even (Succ Zero)     = False
even Zero            = True

div3 (Succ (Succ (Succ n))) = m
  where m = div3 n
div3 Zero                   = True
div3 _                      = False

bar x | even x    = A
      | div3 x    = B
      | otherwise = C

-}

-- h x y z = x
-- k x = x

g x y = x

f x = g m m
  where m = g x x

-- No scoping
f' x = g (m x)
  where m y = g y y

-- Scoping;
f'' x = g (m x)
  where m x = g x x

{-
f x y = g (m x) (m y)
  where m z = h n n z
            where n = k x
-}