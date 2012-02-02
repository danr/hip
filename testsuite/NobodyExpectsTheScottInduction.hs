-- Lists and functions, many properties come from QuickSpec
module ListFunctions where

import AutoPrelude
import Prelude (Eq,Ord,Show,iterate,(!!),fmap,Bool(..),Int)

iter :: (a -> a) -> a -> [a]
iter f x = x : iter f (f x)

doublemap :: (a -> b) -> [a] -> [b]
doublemap f [] = []
doublemap f [x] = [f x]
doublemap f (x:y:zs) = f x:f y:doublemap f zs

prop_doublemap_iter :: (a -> a) -> a -> Prop [a]
prop_doublemap_iter f x = doublemap f (iter f x) =:= iter f (f x)

doublemap' :: (a -> b) -> [a] -> [b]
doublemap' f [] = []
doublemap' f (x:xs) = f x : case xs of
                               []   -> []
                               y:zs -> f y : doublemap' f zs

prop_doublemap'_iter :: (a -> a) -> a -> Prop [a]
prop_doublemap'_iter f x = doublemap' f (iter f x) =:= iter f (f x)

-- This needs depth 2 on structural induction
-- Is it possible to prove this with take lemma? Maybe it's time to upvote take lemma.
prop_doublemaps :: Prop ((a -> b) -> [a] -> [b])
prop_doublemaps = doublemap =:= doublemap'

finite :: [a] -> Bool
finite [] = True
finite (x:xs) = finite xs

prop_all_lists_finite :: [a] -> Prop Bool
prop_all_lists_finite xs = finite xs =:= True