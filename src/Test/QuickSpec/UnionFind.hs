module Test.QuickSpec.UnionFind
       (UF, Replacement((:>)), newSym, (=:=), rep, frozen, runUF, S, isRep) where

import Prelude hiding (min)
import Control.Monad.State.Strict
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap

data S = S {
      links :: IntMap Int,
      sym :: Int
    }

type UF = State S
data Replacement = Int :> Int

runUF :: Int -> UF a -> a
runUF numSyms m = fst (runState m (S IntMap.empty numSyms))

modifyLinks f = modify (\s -> s { links = f (links s) })
modifySym f = modify (\s -> s { sym = f (sym s) })
putLinks l = modifyLinks (const l)

newSym :: UF Int
newSym = do
  s <- get
  modifySym (+1)
  return (sym s)

(=:=) :: Int -> Int -> UF (Maybe Replacement)
s =:= t | s == t = return Nothing
s =:= t = do
  rs <- rep s
  rt <- rep t
  if (rs /= rt) then do
    modifyLinks (IntMap.insert rs rt)
    return (Just (rs :> rt))
   else return Nothing

rep :: Int -> UF Int
rep t = do
  m <- fmap links get
  case IntMap.lookup t m of
    Nothing -> return t
    Just t' -> do
      r <- rep t'
      when (t' /= r) $ modifyLinks (IntMap.insert t r)
      return r

isRep :: Int -> UF Bool
isRep t = do
  t' <- frozen (rep t)
  return (t == t')

frozen :: UF a -> UF a
frozen x = fmap (evalState x) get