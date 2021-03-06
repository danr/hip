module Hip.Util
       (unlist,avgList,selections,withPrevious,concatMapM,concatMaybe
       ,isOp,putEither,mif,countBy,groupSortedOn,nubSorted)
       where

import Data.Maybe
import Data.List
import Data.Function
import Data.Ord
import Test.QuickCheck

unlist :: a -> ([b] -> a) -> [b] -> a
unlist d f [] = d
unlist d f xs = f xs

avgList :: Integral a => [a] -> a
avgList xs = sum xs `div` genericLength xs

-- | Pair up a list with its previous and next elements
--
-- > selections "abc" = [("",'a',"bc"),("a",'b',"c"),("ab",'c',"")]
selections :: [a] -> [([a],a,[a])]
selections xs = map (fromSplit . (`splitAt` xs)) [0..length xs-1]
  where fromSplit (as,b:bs) = (as,b,bs)
        fromSplit _         = error "selections fromSplit unreachable"

-- | Pair up a list with its previous elements
--
-- > withPrevious "abc" = [('a',""),('b',"a"),('c',"ab")]
withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)

-- | If true, put in right, if false, put in left
putEither :: Bool -> a -> Either a a
putEither True  = Right
putEither False = Left

-- | Is this a haskell operator?
isOp :: String -> Bool
isOp = all (`elem` opsyms)
  where opsyms :: String
        opsyms = "!#$%*+./<=>?\\^|:-~@"

-- | concatMapM
concatMapM :: (Functor m,Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . mapM f

-- | If any is nothing (unreachable branch etc), return nothing,
--   otherwise return just the catMaybes.
concatMaybe :: [Maybe [a]] -> Maybe [a]
concatMaybe = fmap concat . sequence

-- | Alternative implementation
concatMaybe' :: [Maybe [a]] -> Maybe [a]
concatMaybe' ms | any isNothing ms = Nothing
                | otherwise        = Just (concat (catMaybes ms))

-- | Test equality of implementations
prop_concats :: [Maybe [Bool]] -> Bool
prop_concats ms = concatMaybe ms == concatMaybe' ms

-- | Monadic if
mif :: Monad m => m Bool -> m a -> m a -> m a
mif mb mt mf = do
   b <- mb
   if b then mt else mf

nubSorted :: Ord a => [a] -> [a]
nubSorted = map head . group . sort

-- | Count the number of occurences satisfying the predicate
countBy :: (a -> Bool) -> [a] -> Int
countBy = (length .) . filter

groupSortedOn :: (Eq b,Ord b) => (a -> b) -> [a] -> [[a]]
groupSortedOn f = groupBy ((==) `on` f)
                . sortBy (comparing f)