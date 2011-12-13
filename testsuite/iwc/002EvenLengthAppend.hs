-- Even length append
-- Specialised with unary natural numbers
-- http://www.csc.liv.ac.uk/~lad/research/challenges/IWC002.txt

data Nat = S Nat | Z

len [] = Z
len (x:xs) = S (len xs)

even' Z = True
even' (S Z) = False
even' (S (S x)) = even' x

[]     `app` ys = ys
(x:xs) `app` ys = x : (xs `app` ys)

prop_evenLengthAppend :: [Int] -> [Int] -> Bool
prop_evenLengthAppend xs ys = even' (len (xs `app` ys)) == even' (len (ys `app` xs))