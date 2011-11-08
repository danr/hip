
map f (x:xs) = f x : map f xs
map f [] = []

map2 f (x:y:ys) = f x : f y : map f ys
map2 f [x] = [f x]
map2 f [] = []

map3 f (x:y:z:zs) = f x : f y : f z : map f zs
map3 f [x,y] = [f x, f y]
map3 f [x] = [f x]
map3 f [] = []

iterate f x = x : iterate f (f x)

iterate2 f x = x : f x : iterate f (f (f x))

iterate3 f x = x : f x : f (f x) : iterate f (f (f (f x)))

data N = S N | Z

approx (S n) []     = []
approx (S n) (x:xs) = x:approx n xs