module Main where

import Data.List.Split
import Control.Applicative
import Data.List
import Control.Arrow

data Tech = StrInd | FPI | Plain | Approx
  deriving (Eq,Ord,Enum,Bounded)

techs :: [Tech]
techs = [minBound..maxBound]

instance Show Tech where
  show StrInd = "  structural induction"
  show FPI    = "  fixed point induction"
  show Plain  = "  plain"
  show Approx = "  approximation lemma"

short :: Tech -> Char
short FPI    = 'F'
short Approx = 'A'
short Plain  = 'P'
short StrInd = 'S'

main = do
   s <- readFile "times.data"
   let propbyprop = (split . keepDelimsL . whenElt) (("prop" ==) . take 4) (lines s)
--   mapM_ (\grp -> mapM_ putStrLn grp >> print (handleGroup grp) >> putStrLn "") propbyprop
--   mapM_ (\grp -> print (handleGroup grp)) propbyprop
   let res = flattenGroups (map handleGroup propbyprop)
--   mapM_ (\(i,g) -> putStrLn (show g ++ " : " ++ show i)) res
   mapM_ (\(i,g) -> putStrLn $ "\\newcommand\\res" ++ map short g ++ "[0]{" ++ show i ++ "}") res

-- Reports which techniques worked for a property
handleGroup :: [String] -> [Tech]
handleGroup (p:ps) | " Theorem" `isSuffixOf` p = nub [ t
                                                     | t <- techs
                                                     , r <- ps
                                                     , show t `isPrefixOf` r
                                                     , " Theorem" `isSuffixOf` r ]
handleGroup _  = []

flattenGroups :: [[Tech]] -> [(Int,[Tech])]
flattenGroups = map (length &&& head) . group .  sort