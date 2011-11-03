
{-
-- k3 x y z = x
-- i x = x

r x y = k (m x) (m y)
  where m z = k3 n n z
            where n = i x
-}

k x y = x

f x = k m m
  where m = k x x

-- No scopink
f' x = k (m x)
  where m y = k y y

-- Scopink;
f'' x = k (m x)
  where m x = k x x

