
{-
-- k3 x y z = x
-- i x = x

r x y = k (m x) (m y)
  where m z = k3 n n z
            where n = i x
-}

k x y = x

f x y = k m m
  where m = k x x

-- No scoping
g x y = k (n x)
  where n y = k x y

-- Scoping;
h x y = k (m x)
  where m x = k x y

