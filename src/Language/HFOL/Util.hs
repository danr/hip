module Language.HFOL.Util where

import Data.List

selections :: [a] -> [([a],a,[a])]
selections xs = map (fromSplit . (`splitAt` xs)) [0..length xs-1]
  where fromSplit (as,b:bs) = (as,b,bs)

withPrevious :: [a] -> [(a,[a])]
withPrevious xs = zip xs (inits xs)
