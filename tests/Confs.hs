
data Nat = S Nat | Z
  deriving (Eq,Show)

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

--prop_L7 :: a -> a -> [a] -> Nat -> Nat -> Nat -> Prop [a]
--prop_L7 x y z w v u = drop (S u) (drop v (drop (S w) (x:y:z))) =:= drop (S u) (drop v (drop w (x:z)))

data Tree a = Empty | Branch (Tree a) a (Tree a)
  deriving (Show)

prop_fmap_id :: Tree a -> Prop (Tree a)
prop_fmap_id t = fmap id t =:= t

id x = x

fmap :: (a -> b) -> Tree a -> Tree b
fmap f Empty = Empty
fmap f (Branch l x r) = Branch (fmap f l) (f x) (fmap f r)
