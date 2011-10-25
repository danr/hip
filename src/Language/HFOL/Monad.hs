{-# LANGUAGE GeneralizedNewtypeDeriving,
             TemplateHaskell,
             TypeOperators,
             FlexibleContexts #-}
module Language.HFOL.Monad
       (TM()
       ,runTM
       ,Debug
       ,write
       ,writeDelimiter
       ,indented
       ,popDebug
       ,returnWithDebug
       ,locally
       ,Bound(..)
       ,boundCon
       ,lookupName
       ,lookupArity
       ,lookupProj
       ,popQuantified
       ,addIndirection
       ,bindNames
       ,bindPattern
       ,makeFunPtrName
       ,addFuns
       ,addCons
       ,useFunPtr
       ,appFold
       ,envStDecls
       ) where

import Prelude hiding ((.),id)
import Control.Category
import Data.Label (mkLabels)
import Data.Label.PureM

import Language.HFOL.Core
import Language.HFOL.Pretty
import Language.HFOL.Bottom

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)

import Control.Applicative
import Control.Monad
import Control.Monad.State hiding (gets,modify)

import Data.Maybe
import Data.List


import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

-- | The TM monad.
--
--   Used to be a RWS, but for convenience everything is in State,
--   even debug output to easier pair it up with accompanying code
--
--   The state capabilities are kept abstract
newtype TM a = TM (State St a)
  deriving (Functor,Applicative,Monad)

-- | Runs a computation in an empty environment, with an empty state.
--   The computation's result is returned with the updated state.
runTM :: TM a -> a
runTM (TM m) = evalState m emptySt

data Bound = QuantVar    { quantVar  :: VarName }
           | FunVar      { boundName :: FunName }
           | ConVar      { boundName :: FunName }
           | Indirection { indExpr   :: Expr    }
  deriving(Eq,Ord,Show)

-- | Is a bound variable a constructor?
boundCon :: Bound -> Bool
boundCon (ConVar _) = True
boundCon _          = False

-- | The empty state
emptySt :: St
emptySt = St { _arities     = M.empty
             , _conProj     = M.empty
             , _conFam      = M.empty
             , _datatypes   = []
             , _usedFunPtrs = S.empty
             , _boundNames  = M.empty
             , _quantified  = S.empty
             , _namesupply  = [ T.VarName ('X' : show x) | x <- [(0 :: Integer)..] ]
             , _debug       = []
             , _debugIndent = 0
             }

-- | The type of debug messages
type Debug = [String]

data St = St { _arities     :: Map Name Int
               -- ^ Arity of functions and constructors
             , _conProj     :: Map Name [Name]
               -- ^ Projection functions for constructors
             , _conFam      :: Map Name [Name]
               -- ^ The other constructors for a given constructor (so far unused)
             , _datatypes   :: [[(Name,Int)]]
               -- ^ The datatypes in the program
             , _usedFunPtrs :: Set Name
               -- ^ Which functions we need to produce ptr conversions for
             , _boundNames  :: Map Name Bound
               -- ^ TPTP name of functions and constructors and quantified variables
             , _quantified  :: Set VarName
               -- ^ Variables to quantify over
             , _namesupply  :: [VarName]
               -- ^ Supply of variables
             , _debug       :: Debug
               -- ^ Debug messages
             , _debugIndent :: Int
               -- ^ Indentation depth for debug messages
             } deriving (Show)
$(mkLabels [''St])

-- | Write a debug delimiter (a newline)
writeDelimiter :: TM ()
writeDelimiter = write ""

-- | Writes a debug message
write :: String -> TM ()
write = TM . write'

write' :: (MonadState St m) => String -> m ()
write' s = do
  i <- gets debugIndent
  modify debug ((replicate (i*2) ' ' ++ s):)

-- | Do an action with indented debug messages
indented :: TM a -> TM a
indented (TM m) = TM $ do
  modify debugIndent succ
  r <- m
  modify debugIndent pred
  return r

-- | Pop and return the debug messages
popDebug :: TM Debug
popDebug = TM $ do
  r <- reverse <$> gets debug
  puts debug []
  return r

-- | Perform an action and pop its debug messages and return in a tuple
returnWithDebug :: TM a -> TM (a,Debug)
returnWithDebug m = liftM2 (,) m popDebug

-- | Locally manipulate boundNames
locally :: TM a -> TM a
locally (TM m) = TM (locally' m)

locally' :: (MonadState St m) => m a -> m a
locally' m = do
  boundNames' <- gets boundNames
  r <- m
  puts boundNames boundNames'
  return r

-- | Insert /n/ elements to a map of /m/ elements
--
--   /O(n * log(m+n))/
insertMany :: Ord k => [(k,v)] -> Map k v -> Map k v
insertMany kvs m = foldr (uncurry M.insert) m kvs

-- | Looks up if a name is a variable or a function/constructor
lookupName :: Name -> TM Bound
lookupName n = TM $ do
    mn <- M.lookup n <$> gets boundNames
    case mn of
      Just b  -> return b
      Nothing -> do -- Variable is unbound, quantify over it
        q <- head <$> gets namesupply
        let qv = QuantVar q
        write' $ "New quantified variable " ++ show q ++ " for " ++ n
        modify boundNames (M.insert n qv)
        modify namesupply tail
        modify quantified (S.insert q)
        return qv

-- | Add a new indirection
addIndirection :: Name -> Expr -> TM ()
addIndirection n e = TM $ do
    write' $ "indirection: " ++ n ++ " := " ++ prettyCore e
    modify boundNames (M.insert n (Indirection e))

-- | Pop and return the quantified variables
popQuantified :: TM [VarName]
popQuantified = TM $ do
  qs <- S.toList <$> gets quantified
  puts quantified S.empty
  return qs

-- | fromMaybe with unbound error message from a function
fromUnbound :: String -> Name -> Maybe a -> a
fromUnbound fn n = fromMaybe (error $ fn ++ ", unbound: " ++ n)

-- | Looks up an arity of a function or constructor
lookupArity :: Name -> TM Int
lookupArity n = TM $ (fromUnbound "lookupArity" n . M.lookup n) <$> gets arities

-- | Looks up the projections for a constructor
lookupProj :: Name -> TM [FunName]
lookupProj n = TM $ (fmap FunName . fromUnbound "lookupProj" n . M.lookup n)
                 <$> gets conProj

-- | Binds the names to quantified variables inside the action
bindNames :: [Name] -> ([VarName] -> TM a) -> TM a
bindNames ns vm = TM $ do
    let l = length ns
    vs <- take l <$> gets namesupply
    let TM m = vm vs
    modify namesupply (drop l)
    locally' $ do
      modify boundNames (insertMany (zipWith (\n v -> (n,QuantVar v)) ns vs))
      m

-- | Bind all variables in a pattern
bindPattern :: Pattern -> ([VarName] -> TM a) -> TM a
bindPattern p m = bindNames (fv p) m
  where
    fv PWild       = []
    fv (PVar x)    = [x]
    fv (PCon _ xs) = concatMap fv xs

-- | Make a pointer name of a name
makePtrName :: Name -> Name
makePtrName n = n ++ "_ptr"

-- | Make a pointer of a function name
makeFunPtrName :: FunName -> FunName
makeFunPtrName = FunName . makePtrName . funName

-- | Add functions/constructor name and arity.
addNameAndArity :: MonadState St m => (FunName -> Bound) -> [(Name,Int)] -> m ()
addNameAndArity mk funs = do
   modify boundNames (insertMany [(n,mk (FunName n))| (n,_) <- funs])
   modify arities (insertMany funs)

-- | Add functions name and arity
addFuns :: [(Name,Int)] -> TM ()
addFuns = TM . addNameAndArity FunVar

-- | Add a datatype's constructor given the arities
--   Projections are also generated
addCons :: [[(Name,Int)]] -> TM ()
addCons css = TM $ do
     addNameAndArity ConVar (concat css)
     addNameAndArity ConVar (concat css)
     modify conFam (insertMany fams)
     modify conProj (insertMany projs)
     modify datatypes (css ++)
  where
    fams  = [ (c,cs')    | cs <- css, let cs' = map fst cs, c <- cs']
    projs = [ projName c | cs <- css, c <- cs]

    projName :: (Name,Int) -> (Name,[Name])
    projName (c,n) = (c,[c ++ "." ++ show x  | x <- [0..n-1]])

-- | Mark a pointer as used
useFunPtr :: Name -> TM ()
useFunPtr fn = TM $ modify usedFunPtrs (S.insert fn)

-- | Make a number of new variable names
makeVarNames :: Int -> [T.VarName]
makeVarNames n = [ T.VarName ('X' : show x) | x <- [0..n-1] ]

-- | Fold the function app over the arguments
--
-- > appFold f [x,y,z] = app(app(app(f,x),y),z)
-- > appFold f []      = f
appFold :: T.Term -> [T.Term] -> T.Term
appFold = foldl (\f x -> T.Fun (T.FunName "app") [f,x])

-- | All FOL declarations from an environment and state
envStDecls :: TM [T.Decl]
envStDecls = TM $ do
  s <- get
  return (projDecls (_conProj s) ++
          ptrDecls (_arities s) (_usedFunPtrs s) ++
          disjDecls (_datatypes s) )

-- | Make datatypes disjunct.
--
-- > data Maybe = Just a | Nothing
--
-- gives
--
-- > forall x . just x != nothing
-- > forall x . just x != bottom
-- > forall x . nothing != bottom
disjDecls :: [[(Name,Int)]] -> [T.Decl]
disjDecls = concatMap datatypeDisj
  where
    -- Make this datatype's constructors and bottom disjunct
    datatypeDisj :: [(Name,Int)] -> [T.Decl]
    datatypeDisj ctors = concat (zipWith constrDisj ctors' (tail (tails ctors')))
      where ctors' = (bottomName,0) : ctors

    -- Make this constructor unequal to all the constructors in the list
    constrDisj :: (Name,Int) -> [(Name,Int)] -> [T.Decl]
    constrDisj x = map (disjunct x) . filter ((fst x /=) . fst)
                                   -- ^ avoid making bottom/=bottom

    -- Make two constructors disjunct
    disjunct :: (Name,Int) -> (Name,Int) -> T.Decl
    disjunct (c1,a1) (c2,a2) = T.Axiom ("axiomdisj" ++ c1 ++ c2)
       $ forall (xs ++ ys) $ Fun (FunName c1) (map T.Var xs)
                               !=
                             Fun (FunName c2) (map T.Var ys)

      where (xs,ys) = splitAt a1 (makeVarNames (a1 + a2))

-- | Make projection declarations
projDecls :: Map Name [Name] -> [T.Decl]
projDecls = concatMap (uncurry mkDecl) . M.toList
  where
    mkDecl :: Name -> [Name] -> [T.Decl]
    mkDecl c ps = zipWith (\x p -> Axiom ("axiom" ++ p)
                                 $ forall xs $ Fun (FunName p)
                                                [Fun (FunName c) (map T.Var xs)]
                                               === T.Var x)
                          xs ps
      where arity = length ps
            xs    = makeVarNames arity

-- | Make pointer declarations
ptrDecls :: Map Name Int -> Set Name -> [T.Decl]
ptrDecls as = map mkDecl . S.toList
  where
    mkDecl fn = Axiom ("ptr" ++ fn)
              $ forall xs
                $ appFold (T.Var (VarName (makePtrName fn)))
                                   (map T.Var xs)
                         ===
                         (Fun (FunName fn) (map T.Var xs))
      where arity = as M.! fn
            xs    = makeVarNames arity
