{-# LANGUAGE ScopedTypeVariables #-}
-- From Data.List http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#sort

-- import Prelude (Show,Eq(..),(.),otherwise)

-- data Ordering = LT | EQ | GT deriving (Show,Eq)

sortBy :: forall a . (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp = mergeAll . sequences
  where
    sequences :: [a] -> [[a]]
    sequences (a:b:xs)
      | a `cmp` b == GT = descending b [a]  xs
      | otherwise       = ascending  b (a:) xs
    sequences xs = [xs]

    descending :: a -> [a] -> [a] -> [[a]]
    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending :: a -> ([a] -> [a]) -> [a] -> [[a]]
    ascending a as (b:bs)
      | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = as [a]: sequences bs

    mergeAll :: [[a]] -> [a]
    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs :: [[a]] -> [[a]]
    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge :: [a] -> [a] -> [a]
    merge as@(a:as') bs@(b:bs')
      | a `cmp` b == GT = b:merge as  bs'
      | otherwise       = a:merge as' bs
    merge [] bs         = bs
    merge as []         = as