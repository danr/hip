module Main where

import Data.List.Split
import Control.Applicative
import Data.List
import Control.Arrow
import Data.Function
import Data.Maybe

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
   s <- readFile "bigoutput"
   let propbyprop = (split . keepDelimsL . whenElt) (("prop" ==) . take 4)
                    (prependFilename s)
       res = flattenGroups (mapMaybe handleGroup propbyprop)
   mapM_ (\(i,(g,_)) -> putStrLn $ "\\newcommand\\res" ++ map short g ++ "[0]{" ++ show i ++ "}") res
   mapM_ (\(i,(g,ps)) -> putStrLn (unwords (map show g)) >> mapM_ putStrLn ps >> putStrLn "") res
--   mapM_ print propbyprop

prependFilename :: String -> [String]
prependFilename = go . dropWhile ("/home" `isPrefixOf`) . lines
  where
    go :: [String] -> [String]
    go (file:ss) =
       let (ps,rest) = break ("/home" `isPrefixOf`) ss
           file' = (reverse . drop 1 . takeWhile (/= '/') . reverse) file
       in  map (addFilename file') ps ++ go rest
    go [] = []

    addFilename file p
       | "prop" `isPrefixOf` p =
         let (p',':':r) = break (== ':') p
         in  p' ++ "(" ++ file ++ "):" ++ r
       | otherwise = p


-- Reports which techniques worked for a property
handleGroup :: [String] -> Maybe ([Tech],String)
handleGroup (p:ps)
  | " Theorem" `isSuffixOf` p = Just (nub [ t
                                          | t <- techs
                                          , r <- ps
                                          , show t `isPrefixOf` r
                                          , " Theorem" `isSuffixOf` r ]
                                     ,takeWhile (/= ':') p)
handleGroup _ = Nothing

flattenGroups :: [([Tech],String)] -> [(Int,([Tech],[String]))]
flattenGroups = map (length &&& (fst . head &&& map snd))
              . groupBy ((==) `on` fst)
              . sortBy (compare `on` fst)