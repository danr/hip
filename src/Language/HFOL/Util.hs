module Language.HFOL.Util (selections,withPrevious,concatMaybe) where

import Data.Maybe
import Data.List
import Test.QuickCheck

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
