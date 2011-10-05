-- Based on the paper "Proof-producing Congruence Closure".

module Test.QuickSpec.CongruenceClosure
       (CC, newSym, (=:=), (=?=), rep, runCC, ($$), S, frozen, funUse, argUse, lookup) where

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Test.QuickSpec.UnionFind(UF, Replacement((:>)))
import qualified Test.QuickSpec.UnionFind as UF
import Data.Maybe
import Data.List(foldl')
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Monadic
import Text.Printf

lookup2 :: Int -> Int -> IntMap (IntMap a) -> Maybe a
lookup2 k1 k2 m = IntMap.lookup k2 (IntMap.findWithDefault IntMap.empty k1 m)

insert2 :: Int -> Int -> a -> IntMap (IntMap a) -> IntMap (IntMap a)
insert2 k1 k2 v m = IntMap.insertWith IntMap.union k1 (IntMap.singleton k2 v) m

delete2 :: Int -> Int -> IntMap (IntMap a) -> IntMap (IntMap a)
delete2 k1 k2 m = IntMap.adjust (IntMap.delete k2) k1 m

data FlatEqn = (Int, Int) := Int deriving (Eq, Ord)

data S = S {
      -- in all these maps, the keys are representatives, the values may not be
      funUse :: !(IntMap [(Int, Int)]),
      argUse :: !(IntMap [(Int, Int)]),
      lookup :: IntMap (IntMap Int)
    }

type CC = StateT S UF

invariant :: String -> CC ()
invariant _ = return ()
-- invariant str = do
--   S funUse argUse lookup <- get
--   -- keys of all maps are representatives
--   let check phase x = do
--        b <- lift (UF.isRep x)
--        if b then return () else error (printf "%s, %s appears as a key in %s but is not a rep in:\nfunUse=%s\nargUse=%s\nlookup=%s" str (show x) phase (show funUse) (show argUse) (show lookup))
--   mapM_ (check "funUse") (IntMap.keys funUse)
--   mapM_ (check "argUse") (IntMap.keys argUse)
--   mapM_ (check "lookup") (IntMap.keys lookup)
--   mapM_ (mapM_ (check "inner lookup") . IntMap.keys) (IntMap.elems lookup)

modifyFunUse f = modify (\s -> s { funUse = f (funUse s) })
modifyArgUse f = modify (\s -> s { argUse = f (argUse s) })
addFunUses xs s = modifyFunUse (IntMap.insertWith (++) s xs)
addArgUses xs s = modifyArgUse (IntMap.insertWith (++) s xs)
modifyLookup f = modify (\s -> s { lookup = f (lookup s) })
putLookup l = modifyLookup (const l)

newSym :: CC Int
newSym = lift UF.newSym

($$) :: Int -> Int -> CC Int
f $$ x = do
  invariant (printf "before %s$$%s" (show f) (show x))
  m <- gets lookup
  f' <- rep f
  x' <- rep x
  invariant (printf "at %s$$%s:1" (show f) (show x))
  case lookup2 x' f' m of
    Nothing -> do
      c <- newSym
      invariant (printf "at %s$$%s:2" (show f) (show x))
      putLookup (insert2 x' f' c m)
      addFunUses [(x', c)] f'
      addArgUses [(f', c)] x'
      invariant (printf "after %s$$%s" (show f) (show x))
      return c
    Just k -> return k

(=:=) :: Int -> Int -> CC Bool
a =:= b = propagate (a, b)

(=?=) :: Int -> Int -> CC Bool
t =?= u = liftM2 (==) (rep t) (rep u)

propagate (a, b) = do
  (unified, pending) <- propagate1 (a, b)
  mapM_ propagate pending
  return unified

propagate1 (a, b) = do
  invariant (printf "before propagate (%s, %s)" (show a) (show b))
  res <- lift (a UF.=:= b)
  case res of
    Nothing -> return (False, [])
    Just (r :> r') -> do
      funUses <- gets (IntMap.lookup r . funUse)
      argUses <- gets (IntMap.lookup r . argUse)
      case (funUses, argUses) of
        (Nothing, Nothing) -> return (True, [])
        _ -> fmap (\x -> (True, x)) (updateUses r r' (fromMaybe [] funUses) (fromMaybe [] argUses))

updateUses r r' funUses argUses = do
  modifyFunUse (IntMap.delete r)
  modifyArgUse (IntMap.delete r)
  modifyLookup (IntMap.delete r)
  forM_ funUses $ \(x, _) -> do
    x' <- rep x
    modifyLookup (delete2 x' r)
  invariant (printf "after deleting %s" (show r))
  let repPair (x, c) = do
        x' <- rep x
        return (x', c)
  funUses' <- mapM repPair funUses
  argUses' <- mapM repPair argUses

  m <- gets lookup

  let foldUses insert lookup pending m uses = foldl' op e uses
        where op (pending, newUses, m) (x', c) =
                case lookup x' m of
                  Just k -> ((c, k):pending, newUses, m)
                  Nothing -> (pending, (x', c):newUses, insert x' c m)
              e = (pending, [], m)

      (funPending, funNewUses, m') = foldUses (\x' c m -> insert2 x' r' c m)
                                              (\x' m -> lookup2 x' r' m)
                                              [] m funUses'

      (pending, argNewUses, argM) = foldUses IntMap.insert IntMap.lookup funPending
                                             (IntMap.findWithDefault IntMap.empty r' m')
                                             argUses'

  addFunUses funNewUses r'
  addArgUses argNewUses r'

  putLookup (if IntMap.null argM then m' else IntMap.insert r' argM m')
  invariant (printf "after updateUses (%s, %s)" (show r) (show r'))

  return pending

rep :: Int -> CC Int
rep s = lift (UF.rep s)

frozen :: CC a -> CC a
frozen x = get >>= lift . UF.frozen . evalStateT x

runCC :: Int -> CC a -> a
runCC numSyms m = UF.runUF numSyms (evalStateT m (S IntMap.empty IntMap.empty IntMap.empty))

-- QuickCheck properties.

data Action = NewSym | Apply Int Int | Unify Int Int | Rep Int deriving Show
newtype Actions = Actions [Action] deriving Show

instance Arbitrary Actions where
  arbitrary = fmap Actions (actions 0)
  shrink (Actions as) = map Actions (filter (valid 0) (shrinkList shr as))
    where shr NewSym = []
          shr (Apply x y) = NewSym:[ Apply x' y' | (x', y') <- shrink (x, y) ]
          shr (Unify x y) = [ Unify x' y' | (x', y') <- shrink (x, y) ]
          shr (Rep x) = [ Rep x' | x' <- shrink x ]

          valid n (NewSym:as) = valid (n+1) as
          valid n (Apply f x:as) = bound n f && bound n x && valid (n+1) as
          valid n (Unify x y:as) = bound n x && bound n y && valid n as
          valid n (Rep x:as) = bound n x && valid n as
          valid _ [] = True

          bound n x = 0 <= x && x < n

exec :: [Action] -> [Int] -> CC [Int]
exec [] xs = return xs
exec (NewSym:as) xs = newSym >>= \x -> exec as (xs ++ [x])
exec (Apply f x:as) xs = (xs !! f) $$ (xs !! x) >>= \y -> exec as (xs ++ [y])
exec (Unify x y:as) xs = (xs !! x) =:= (xs !! y) >> exec as xs
exec (Rep x:as) xs = rep (xs !! x) >> exec as xs

actions :: Int -> Gen [Action]
actions 0 =
  frequency [(25, liftM (NewSym:) (actions 1)),
             (1, return [])]
actions n =
  frequency [(2, liftM (NewSym:) (actions (n+1))),
             (2, liftM3 (\f x as -> Apply f x:as) element element (actions (n+1))),
             (2, liftM2 (:) (liftM Rep element) (actions n)),
             (2, liftM2 (:) (liftM2 Unify element element) (actions n)),
             (1, return [])]
    where element = choose (0, n-1)

var :: [Int] -> PropertyM CC (Int, Int)
var xs = do
  pre (not (null xs))
  x <- pick (elements xs)
  x' <- freeze (rep x)
  return (x, x')

data Term = Var Int | ApplyT Term Term deriving Show

term :: Int -> Gen Term
term n = sized f
  where f 0 = fmap Var (choose (0, n-1))
        f n = oneof [f 0, liftM2 ApplyT (f (n `div` 2)) (f (n `div` 2))]

evalTerm :: [Int] -> Term -> CC Int
evalTerm vs (Var x) = return (vs !! x)
evalTerm vs (ApplyT f x) = join (liftM2 ($$) (evalTerm vs f) (evalTerm vs x))

forAllStates :: ([Int] -> PropertyM CC a) -> Actions -> Property
forAllStates p (Actions as) = runProp (run (exec as []) >>= p)

runProp :: PropertyM CC a -> Property
runProp p = monadic (runCC 0) p

freeze :: CC a -> PropertyM CC a
freeze x = run (frozen x)

prop_RepIdempotent = forAllStates $ \vars -> do
  (x, x') <- var vars
  x'' <- freeze (rep x')
  assert (x' == x'')

prop_AppPreservesRep = forAllStates $ \vars -> do
  pre (not (null vars))
  reps <- freeze (mapM rep vars)
  t <- pick (term (length vars))
  t1 <- freeze (evalTerm vars t >>= rep)
  t2 <- freeze (evalTerm reps t)
  assert (t1 == t2)
-- counterexample (only means: $$ doesn't always produce a rep. does it matter?)
-- Actions [NewSym,Apply 0 0,Unify 1 0]
-- ApplyT (Var 0) (Var 0)

prop_RepIsId = forAllStates $ \vars -> do
  (x, x') <- var vars
  assert (x == x')
