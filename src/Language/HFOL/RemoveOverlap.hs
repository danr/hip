module Language.HFOL.RemoveOverlap where

import Language.HFOL.Core

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
PCon c1 ps1 <=? PCon c2 ps2 = c1 == c2 && or (zipWith (<=?) ps1 ps2)

-- | A small test :)
test1 :: [Branch]
test1 = [PCon "C" [PVar "x"]            :-> Var "e1"
        ,PCon "C" [PCon "C" [PVar "x"]] :-> Var "e2"
        ,PCon "A" [pcon0 "D",pcon0 "J"] :-> Var "e3"
        ,PCon "A" [pcon0 "D",PVar  "z"] :-> Var "e4"
        ,PCon "A" [PVar  "y",pcon0 "E"] :-> Var "e5"
        ,PVar "x"                       :-> Var "e6"
        ,PVar "_"                       :-> Var "e7"
        ]

