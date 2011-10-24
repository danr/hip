{-

   fixBranches : Remove overlapping branches + Insert bottoms

   moreSpecificPatterns : Get the least more specific patterns than a pattern
                          This function needs more testing

-}

module Language.HFOL.FixBranches (fixBranches,moreSpecificPatterns,bottomName,nameWilds) where

import Language.HFOL.Core
import Language.HFOL.Pretty
import Language.HFOL.ParserInternals
import Language.HFOL.Bottom
import Language.HFOL.Util (selections)
import Control.Applicative
import Control.Monad.State
import Data.List (nubBy)
import Data.Function (on)
import Data.Maybe (listToMaybe,fromMaybe)

import Language.HFOL.ArbitraryCore
import Test.QuickCheck
import Test.QuickCheck.Arbitrary

-- | Adds bottoms for each pattern-matched constructor
--   and removes overlapping patterns
fixBranches :: Expr -> [Branch] -> [Branch]
fixBranches scrut = removeOverlap . (addBottoms scrut)

--------------------------------------------------------------------------------
-- Remove overlapping branches

{-| Removes overlapping branches:

    C x     -> e1
    C (C x) -> e2   -- This branch will be removed
    _       -> e3

   More specifically, removes all branches which has a
   less or equal specific pattern earlier in the branch list

   Instead of using brs ++ [ p :-> e ],
   we use cons and reverse the result.
-}
removeOverlap :: [Branch] -> [Branch]
removeOverlap = reverse . foldl f []
  where
    f brs (p :-> e) | any ((<=? p) . brPat) brs = brs
                    | otherwise                 = p :-> e : brs

removeOverlappingPatterns :: [Pattern] -> [Pattern]
removeOverlappingPatterns = map brPat . removeOverlap . map (:-> undefined)

-- | Less specific than or equal specificity as
(<=?) :: Pattern -> Pattern -> Bool
PCon c1 ps1 <=? PCon c2 ps2 = c1 == c2 && and (zipWith (<=?) ps1 ps2)
PCon _ _    <=? _           = False
_           <=? _           = True

-- | Makes a list of patterns into a list of wild patterns
wild :: [Pattern] -> [Pattern]
wild ps = [ PWild | _ <- ps ]


--------------------------------------------------------------------------------
-- Add bottoms

-- | Adds bottoms. Not in the most efficient way, since we
--   remove overlaps afterwards
addBottoms :: Expr -> [Branch] -> [Branch]
addBottoms scrut brs = concat
         [ (p :-> e) : [ p' :-> bottom
                       | p' <- addBottom scrut' p
                       ]
         | (p :-> e) <- brs
         ]
      ++ [scrut' :-> bottom]
  where matchscrut (Con a as) = PCon a (map matchscrut as)
        matchscrut _          = PWild

        scrut' = matchscrut scrut

-- | What are the bottom patterns for
--
-- > A (B C) (D E) ?
--
-- They are
--
-- > ⊥
-- > A ⊥     _
-- > A _     ⊥
-- > A (B ⊥) _
-- > A _     (D ⊥)

testScr  = parsePattern "A x y"
testScr' = parsePattern "A (B x) y"
testBPS  = parsePattern "A (B C) (D E)"

addBottom :: Pattern -> Pattern -> [Pattern]
addBottom _scrut        PWild       = []
addBottom _scrut        (PVar _)    = []
addBottom (PCon sc sps) (PCon c ps)
     | sc /= c   = []               -- Unreachable clause
     | otherwise = [ PCon c (map fst l ++ [fp] ++ map fst r)
                   | (l,(sp,p),r) <- selections (zip sps ps)
                   , fp <- addBottom sp p
                   ]
addBottom scrut (PCon c ps)         =  bottomP : fails
  where
    fails   = [ PCon c (wild l ++ [fp] ++ wild r)
              | (l,p,r) <- selections ps, fp <- addBottom PWild p
              ]


-- | Gets the more specific patterns, and blanks the arguments
--
--   Now we can removeOverlap on the reverse because we're looking "upwards"
--   the case tree. This enables us to remove duplicate and more specific
--   results.
--
--   TODO: Tidy this up, make it more efficient
--
--   TODO: Make tests
--
-- > moreSpecificPatterns (x:f x) [(x:y:ys),_] = [(f x,_:_)]
testPs = map parsePattern ["Tup2 _ Zero","Tup2 _ bottom"]
testExpr = parseExpr "Tup2 Zero x"


moreSpecificPatterns :: Expr -> [Pattern] -> [[(Expr,Pattern)]]
moreSpecificPatterns e ps = msp e (removeOverlappingPatterns (reverse ps))

msp (Con c as) ps = filter (not . null)
                    [ cc $ zipWith (\a a' -> msp a [a']) as ps'
                    | PCon c' ps' <- ps , c == c']
  where cc = concat . concat
msp e          ps = [ [(e,p)] | p <- ps ]


-- All wilds need to be namen to use moreSpecificPatterns
nameWilds :: Pattern -> Pattern
nameWilds p = evalState (go p) 0
  where
    go :: Pattern -> State Int Pattern
    go PWild       = do { x <- get; modify succ; return (PVar ('_':show x)) }
    go (PCon c ps) = PCon c <$> mapM go ps
    go p           = return p


--------------------------------------------------------------------------------
-- Testing without bottoms

testpat = parsePattern "C2 B0 b"
testbrs = map parseBranch ["C2 Z0 (Z1 (Y1 (B2 (C1 y) _))) -> z","z -> a"]

pickBranch :: Pattern -> [Branch] -> Maybe Expr
pickBranch p = fmap brExpr . listToMaybe . filter (matches p . brPat)

bottomless :: Pattern -> Bool
bottomless (PCon c as) = c /= bottomName && all bottomless as
bottomless _           = True

matches :: Pattern -> Pattern -> Bool
PCon c as `matches` PCon c' as' = and ((c == c') : zipWith matches as as')
_         `matches` c@(PCon{})  = bottomless c
_         `matches` _           = True

prop_removeOverlap :: Pattern -> [Branch] -> Bool
prop_removeOverlap p brs = pickBranch p brs == pickBranch p (removeOverlap brs)

patternFromScrut :: Expr -> Gen Pattern
patternFromScrut (Con c as) = PCon c <$> mapM patternFromScrut as
patternFromScrut _          = arbitrary

prop_addBottoms :: Expr -> [Branch] -> Property
prop_addBottoms scrut brs = forAll (patternFromScrut scrut) $ \p ->
                            Just (fromMaybe bottom (pickBranch p brs))
                         == pickBranch p (addBottoms scrut brs)

prop_fixBranches :: Expr -> [Branch] -> Property
prop_fixBranches scrut brs = forAll (patternFromScrut scrut) $ \p ->
                             Just (fromMaybe bottom (pickBranch p brs))
                          == pickBranch p (fixBranches scrut brs)

-- Testing with bottoms

data Match = Mismatch | Match | Bottom deriving (Eq,Ord,Show)

-- If all matches, return match
-- if any is bottom, return bottom
-- otherwise return bottom
foldMatches :: [Match] -> Match
foldMatches ms | any (== Bottom) ms = Bottom
               | all (== Match)  ms = Match
               | otherwise          = Mismatch

matchesBottom :: Pattern -> Pattern -> Match
PCon c as `matchesBottom` PCon c' as'
     | c == bottomName = Bottom
     | c == c'         = foldMatches (zipWith matchesBottom as as')
     | otherwise       = Mismatch
_         `matchesBottom` _           = Match

pickBranchBottom :: Pattern -> [Branch] -> Expr
pickBranchBottom p brs = case [ (match,p' :-> e) | p' :-> e <- brs
                                                 , let match = p `matchesBottom` p'
                                                 , match /= Mismatch] of
                               []                 -> bottom      -- non-exhaustive patterns
                               (Bottom,_      ):_ -> bottom
                               (Match ,_ :-> e):_ -> e

botpatFromScrut :: Expr -> Gen Pattern
botpatFromScrut (Con c as) = PCon c <$> mapM botpatFromScrut as
botpatFromScrut _          = unBP <$> arbitrary


prop_addBottoms' :: Expr -> [Branch] -> Property
prop_addBottoms' scrut brs = forAll (botpatFromScrut scrut) $ \p ->
                             case pickBranch p (addBottoms scrut brs) of
                                        Nothing -> False
                                        Just e  -> e == pickBranchBottom p brs


prop_fixBranches' :: Expr -> [Branch] -> Property
prop_fixBranches' scrut brs = forAll (botpatFromScrut scrut) $ \p ->
                             case pickBranch p (fixBranches scrut brs) of
                                        Nothing -> False
                                        Just e  -> e == pickBranchBottom p brs

--------------------------------------------------------------------------------
-- For manual testing

-- | A small test :)
test1 :: [Branch]
test1 = map parseBranch
        ["C x                -> e1"
        ,"C (C x)            -> e2"
        ,"A D J              -> e3"
        ,"A D z              -> e4"
        ,"A y E              -> e5"
        ,"Cons x (Cons y ys) -> e6"
        ,"J (K L) (M N)      -> e7"
        ,"J (K L) (M O)      -> e8"
        ,"J (K r) (M z)      -> e9"
        ,"x                  -> e0"
        ,"_                  -> e9"
        ]
