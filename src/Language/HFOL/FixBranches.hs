{-

   fixBranches : Remove overlapping branches and insert bottoms

   moreSpecificPatterns : Get the least more specific patterns than a pattern
                          This function needs more testing

-}
module Language.HFOL.FixBranches
{-
       (fixBranches,moreSpecificPatterns,nameWilds
       ,addGuardConds,guardCondition
       ,matchAnyBranch
       ,prop_addBottoms,prop_addBottoms'
       ,prop_removeOverlap
       ,prop_fixBranches,prop_fixBranches') where
-}
 where

import Language.HFOL.Core
import Language.HFOL.Pretty
import Language.HFOL.ParserInternals
import Language.HFOL.Constructors

import Language.HFOL.Util
import Control.Applicative
import Control.Monad.State
import Data.List (intersect)
import Data.Maybe (listToMaybe,fromMaybe,catMaybes)

import Language.HFOL.ArbitraryCore
import Test.QuickCheck
import Test.QuickCheck.Arbitrary

-- | Adds bottoms for each pattern-matched constructor
--   and removes overlapping patterns
fixBranches :: Expr -> [Branch] -> [Branch]
fixBranches scrut = removeOverlap . addBottoms scrut

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
    f brs (p :-> e) | any ((<=? p) . brPMG) brs = brs
                    | otherwise                 = p :-> e : brs


removeOverlappingPatterns :: [PMG] -> [PMG]
removeOverlappingPatterns = reverse . foldl f []
  where
    f ps p | any (<=? p) ps = ps
           | otherwise      = p:ps

{-

   With guards:

   b1 -> e1
   b2 -> e2

   If b1 <= b2, remove b2 unless b1 is guarded
   If b1 == b2, keep b2

-}

class Specificity a where
  (<=?) :: a -> a -> Bool

instance Specificity PMG where
  pg <=? pg' = pattern pg <=? pattern pg' && notGuarded pg

-- | Less specific than or equal specificity as
instance Specificity Pattern where
  PCon c1 ps1 <=? PCon c2 ps2 = c1 == c2 && and (zipWith (<=?) ps1 ps2)
  PCon _ _    <=? _           = False
  _           <=? _           = True

--------------------------------------------------------------------------------
-- Add bottoms

-- | Adds bottoms. Not in the most efficient way, since we
--   remove overlaps afterwards
--
--   If there exists a match-any pattern, we need to add all branches
--   with pattern-matched constructors as bottoms. Though, if the
--   match-any pattern goes to bottom, nothing needs to be done.
--   If there is no match-any pattern, just add a new one which goes to bottom.
addBottoms :: Expr -> [Branch] -> [Branch]
addBottoms scrut brs = case matchAnyBranch scrut brs of
  Nothing -> brsBottomGuards ++ [NoGuard PWild :-> bottom]
  Just (p :-> e) | e == bottom -> brsBottomGuards
                 | otherwise -> concat [ (p :-> e) : [ p' :-> bottom
                                                     | p' <- addBottom scrut' p
                                                     ]
                                       | (p :-> e) <- brs
                                       ]
  where matchscrut (Con a as) = PCon a (map matchscrut as)
        matchscrut _          = PWild

        brsBottomGuards = concatMap addBottomGuard brs

        scrut' = matchscrut scrut

-- | Returns the branch that matches anything, if it exists
matchAnyBranch :: Expr -> [Branch] -> Maybe Branch
matchAnyBranch scrut brs = listToMaybe
                           [ pmg :-> e | pmg :-> e <- brs
                           , notGuarded pmg , matchAny scrut (pattern pmg) ]
  where
    -- Is this pattern a default match-all branch?
    matchAny :: Expr -> Pattern -> Bool
    matchAny (Con sc sps) (PCon c ps)
        | sc == c   = and (zipWith matchAny sps ps)
        | otherwise = False
    matchAny _            (PCon _ _) = False
    matchAny _            _          = True

addBottomGuard :: Branch -> [Branch]
addBottomGuard br@(NoGuard p :-> e) = [br]
addBottomGuard br@(Guard p g :-> e) = [br,Guard p (IsBottom g) :-> bottom]

-- | Adds the bottom PMGs for a PMG under a scrutinee
addBottom :: Pattern -> PMG -> [PMG]
addBottom scrut (NoGuard p) = map NoGuard (addBottomPattern scrut p)
addBottom scrut (Guard p g) = Guard p (IsBottom g)
                            : map NoGuard (addBottomPattern scrut p)

-- | Adds the bottom patterns for a pattern under a scrutinee
addBottomPattern :: Pattern -> Pattern -> [Pattern]
addBottomPattern _scrut        PWild       = []
addBottomPattern _scrut        (PVar _)    = []
addBottomPattern (PCon sc sps) (PCon c ps)
     | sc /= c   = []               -- Unreachable clause
     | otherwise = [ PCon c (map fst l ++ [fp] ++ map fst r)
                   | (l,(sp,p),r) <- selections (zip sps ps)
                   , fp <- addBottomPattern sp p ]
addBottomPattern _scrut (PCon c ps) = bottomP : fails
  where
    fails   = [ PCon c (wild l ++ [fp] ++ wild r)
              | (l,p,r) <- selections ps, fp <- addBottomPattern PWild p
              ]

-- | Makes a list of patterns into a list of wild patterns
wild :: [Pattern] -> [Pattern]
wild ps = [ PWild | _ <- ps ]

--------------------------------------------------------------------------------
-- More specific patterns

{-| Gets the more specific patterns
--
--  Now we can removeOverlap on the reverse because we're looking
--  "upwards" the case tree. This enables us to remove duplicate and
--  more specific results.
--
--  TODO: Tidy up
--
--  TODO: Make tests
--
-- > moreSpecificPatterns (x:f x) [(x:y:ys),_] = [(f x,_:_)]
-- > moreSpecificPatterns (x:xs)  [(x:xs | p x)] = [(x,x | p x),(xs,xs)]
-}
moreSpecificPatterns :: Expr -> [PMG] -> [[(Expr,Pattern)]]
moreSpecificPatterns e pmgs = reverse $ filter (not . null) $ catMaybes
   [ addGuardConds (msp e (pattern pmg)) (guardCondition pmg)
   | pmg <- removeOverlappingPatterns (reverse pmgs)
   ]

addGuardConds :: Maybe [a] -> Maybe a -> Maybe [a]
addGuardConds (Just xs) (Just y) = Just (xs ++ [y])
addGuardConds Nothing   _        = Nothing
addGuardConds xs        Nothing  = xs

guardCondition :: PMG -> Maybe (Expr,Pattern)
guardCondition (NoGuard _)            = Nothing
guardCondition (Guard _ (IsBottom e)) = Just (e,bottomP)
guardCondition (Guard _ e           ) = Just (e,trueP)

-- | More specific patterns
msp :: Expr -> Pattern -> Maybe [(Expr,Pattern)]
msp (Con c as) (PCon c' ps) | c == c'   = concatMaybe $ zipWith msp as ps
                            | otherwise = Nothing
msp (Con c as) _            = Just []
msp e          p            = Just [(e,p)]

-- | All wilds need to be named to use moreSpecificPatterns.
--
-- > nameWilds (Tup3 _ x _) = Tup3 _0 x _1
nameWilds :: Pattern -> Pattern
nameWilds = (`evalState` 0) . go
  where
    go :: Pattern -> State Int Pattern
    go PWild       = do { x <- get; modify succ; return (PVar ('_':show x)) }
    go (PCon c ps) = PCon c <$> mapM go ps
    go p           = return p

testPMGs = map (brPMG . parseBranch) ["Cons x xs | p x -> filter"
                                     ]
testExpr = parseExpr "Cons x xs"

testUs = map (brPMG . parseBranch) ["U | eq n m -> e1"
                                   ,"U | lt n m -> e2"
                                   ]

testU = parseExpr "U"

testWs = map (brPMG . parseBranch) ["_ | eq n m -> e1"]

testPrev = map (brPMG . parseBranch)
    [ "T (Cons Zero xs) (Cons (Succ n) ys) -> e"
    , "T Bottom _                          -> e"
    , "T (Cons Bottom _) _                 -> e"
    , "T _ Bottom                          -> e"
    , "T _ (Cons Bottom _)                 -> e"
    ]

testEPrev = parseExpr "T (Cons n zs) b"

{-

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

--------------------------------------------------------------------------------
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

-}

-- | A small test :)
testOverlap :: [Branch]
testOverlap = map parseBranch
        ["C x      | p x     -> e11"
        ,"C x      | p2 x    -> e12"
        ,"C (C x)  | p3 x    -> e21"
        ,"C (C x)            -> e22"
        ,"A D J    | b       -> e3"
        ,"A D z              -> e4"
        ,"A y E              -> e5"
        ,"Cons x (Cons y ys) -> e6"
        ,"J (K L) (M N)      -> e7"
        ,"J (K L) (M O)      -> e8"
        ,"J (K r) (M z)      -> e9"
        ,"x                  -> e0"
        ,"_                  -> e9"
        ]

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

testExpr1    = parsePattern "_"
testExpr2    = parsePattern "A x y"
testExpr3    = parsePattern "A (B x) y"
testPattern  = parsePattern "A (B C) (D E)"
