module Language.HFOL.FixBranches (fixBranches) where

import Language.HFOL.Core
import Language.HFOL.Pretty

-- | Adds bottoms for each pattern-matched constructor
--   and removes overlapping patterns
fixBranches :: [Branch] -> [Branch]
fixBranches = removeOverlap . addBottoms

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

-- | Less specific than or equal specificity as
(<=?) :: Pattern -> Pattern -> Bool
PVar _      <=? PCon _  _   = True
PVar _      <=? PVar _      = True
PCon _ _    <=? PVar _      = False
PCon c1 ps1 <=? PCon c2 ps2 = c1 == c2 && and (zipWith (<=?) ps1 ps2)

-- | A small test :)
test1 :: [Branch]
test1 = [PCon "C" [PVar "x"]            :-> Var "e1"
        ,PCon "C" [PCon "C" [PVar "x"]] :-> Var "e2"
        ,PCon "A" [pcon0 "D",pcon0 "J"] :-> Var "e3"
        ,PCon "A" [pcon0 "D",PVar  "z"] :-> Var "e4"
        ,PCon "A" [PVar  "y",pcon0 "E"] :-> Var "e5"
        ,PCon "Cons" [PVar "x",PCon "Cons" [PVar "y",PVar "ys"]] :-> Var "elist"
        ,PVar "x"                       :-> Var "e6"
        ,PVar "_"                       :-> Var "e7"
        ]

bottomP :: Pattern
bottomP = pcon0 ".Bottom"

bottom :: Expr
bottom = con0 ".Bottom"

selections :: [a] -> [([a],a,[a])]
selections xs = map (fromSplit . (`splitAt` xs)) [0..length xs-1]
  where fromSplit (as,b:bs) = (as,b,bs)

-- | Adds bottoms. Not in the most efficient way, since we
--   remove overlaps afterwards
addBottoms :: [Branch] -> [Branch]
addBottoms = concatMap (\br -> br : map (:-> bottom) (addBottom (brPat br)))

addBottom :: Pattern -> [Pattern]
addBottom (PVar _)    = []
addBottom (PCon c ps) = bottomP : fails
  where
    fails   = [ PCon c (wild l ++ [fp] ++ wild r)
              | (l,p,r) <- selections ps, fp <- addBottom p
              ]
    wild ps = [ PVar "_" | _ <- ps ]

