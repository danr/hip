
-- Pete's nasty problem
-- http://www.csc.liv.ac.uk/~lad/research/challenges/IWC009.txt

data Nat = S Nat | Z
  deriving (Eq,Show)

len [] = Z
len (x:xs) = S (len xs)

[]     `app` ys = ys
(x:xs) `app` ys = x : (xs `app` ys)


is6 (S (S (S (S (S (S Z)))))) = True
is6 _                         = False

splitList :: [a] -> [a] -> [a]
splitList [] w = w
splitList (a:x) w | is6 (len w) = w `app` splitList (a:x) []
                  | otherwise   = splitList x (w `app` [a])

newSplit :: [a] -> [a] -> Nat -> [a]
newSplit []    w d = w
newSplit (a:x) w d | is6 d     = w `app` newSplit (a:x) [] Z
                   | otherwise = newSplit x (w `app` [a]) (S d)

prop_split :: [Int] -> [Int] -> Bool
prop_split x w = newSplit x w (len w) == splitList x w