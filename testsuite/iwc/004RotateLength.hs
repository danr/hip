-- http://www.csc.liv.ac.uk/~lad/research/challenges/IWC004a.txt
-- http://www.csc.liv.ac.uk/~lad/research/challenges/IWC004b.txt

data Nat = S Nat | Z

len [] = Z
len (x:xs) = S (len xs)

[]     `app` ys = ys
(x:xs) `app` ys = x : (xs `app` ys)

rotate Z     xs     = xs
rotate (S n) []     = []
rotate (S n) (x:xs) = rotate n (xs `app` [x])

prop_rotateLength :: [Int] -> Bool
prop_rotateLength xs = rotate (len xs) xs == xs

prop_appAssoc :: [Int] -> [Int] -> [Int] -> Bool
prop_appAssoc xs ys zs =    ((xs `app` ys) `app` zs)
                         == (xs `app` (ys `app` zs)) 

-- In the commentary, it says it needs the property that append is associative
prop_rotateLength2 :: [Int] -> [Int] -> Bool
prop_rotateLength2 xs ys = rotate (len xs) (xs `app` ys) == (ys `app` xs)