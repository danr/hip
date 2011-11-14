{-# LANGUAGE GeneralizedNewtypeDeriving,
             TemplateHaskell,
             TypeOperators,
             ParallelListComp,
             FlexibleContexts #-}
module Language.HFOL.ToFOL.Monad
       (TM()
       ,runTM
       ,Debug
       ,getProofMode
       ,addProofDecl
       ,getProofDecls
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
       ,lookupType
       ,popQuantified
       ,skolem
       ,addIndirection
       ,makeFunPtrName
       ,addTypes
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

import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.ToFOL.Constructors
import Language.HFOL.ToFOL.ProofDatatypes
import Language.HFOL.Util (isOp)

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)

import Control.Applicative
import Control.Monad
import Control.Monad.State hiding (gets,modify)

import Data.Maybe
import Data.List
import Data.Char (toUpper)

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
newtype TM a = TM { unTM :: State St a }
  deriving (Functor,Applicative,Monad)

-- | Runs a computation in an empty environment, with an empty state.
--   The computation's result is returned with the updated state.
runTM :: Bool -> TM a -> a
runTM p (TM m) = evalState m (initSt p)

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
initSt :: Bool -> St
initSt p = St { _arities     = M.empty
              , _conProj     = M.empty
              , _conFam      = M.empty
              , _datatypes   = []
              , _usedFunPtrs = S.empty
              , _boundNames  = M.empty
              , _quantified  = S.empty
              , _debug       = []
              , _debugIndent = 0
              , _namesupply  = [ show x | x <- [(0 :: Integer)..] ]
              , _proofMode   = p
              , _proofDecls  = []
              , _types       = M.empty
              }

-- | The type of debug messages
type Debug = [String]

data St = St { _arities     :: Map Name Int
               -- ^ Arity of functions and constructors
             , _conProj     :: Map Name [Name]
               -- ^ Projection functions for constructors
             , _conFam      :: Map Name [Name]
               -- ^ The constructors for a datatype
             , _datatypes   :: [[(Name,Int)]]
               -- ^ The datatypes in the program
             , _usedFunPtrs :: Set Name
               -- ^ Which functions we need to produce ptr conversions for
             , _boundNames  :: Map Name Bound
               -- ^ TPTP name of funs/costr and quantified variables
             , _quantified  :: Set VarName
               -- ^ Variables to quantify over
             , _debug       :: Debug
               -- ^ Debug messages
             , _debugIndent :: Int
               -- ^ Indentation depth for debug messages
             , _namesupply  :: [Name]
               -- ^ Namesupply, currently only used to rename infix operators
             , _proofMode   :: Bool
               -- ^ Is proof mode on?
             , _proofDecls  :: [ProofDecl]
               -- ^ Proof declarations, i.e propositions to be proved
             , _types       :: Map Name Type
               -- ^ Types of functions and constructors
             } deriving (Show)
$(mkLabels [''St])

-- | Are we currently in proof mode?
getProofMode :: TM Bool
getProofMode = TM $ gets proofMode

-- | Add a proof declaration
addProofDecl :: ProofDecl -> TM ()
addProofDecl d = TM $ modify proofDecls (d:)

-- | Get all proof declarations
getProofDecls :: TM [ProofDecl]
getProofDecls = TM $ reverse <$> gets proofDecls

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

lookupType :: Name -> TM (Maybe Type)
lookupType n = M.lookup n <$> gets types

-- | Looks up if a name is a variable or a function/constructor
lookupName :: Name -> TM Bound
lookupName n@(x:xs) = TM $ do
    mn <- M.lookup n <$> gets boundNames
    case mn of
      Just b  -> return b
      Nothing -> do -- Variable is unbound, quantify over it
        q <- VarName <$> case () of
                   () | x == '_'  -> return ("W_" ++ xs)
                      | isOp n    -> do v <- head <$> gets namesupply
                                        modify namesupply tail
                                        return ("OP_" ++ v)
                      | otherwise -> return (toUpper x:xs)
        let qv = QuantVar q
        write' $ "New quantified variable " ++ show q ++ " for " ++ n
        modify boundNames (M.insert n qv)
        modify quantified (S.insert q)
        return qv
lookupName "" = error "lookupName on empty name"

-- | Makes a new skolem variable for this name
skolem :: Name -> TM Name
skolem n = do
  n' <- (n ++) . head <$> TM (gets namesupply)
  TM $ modify namesupply tail
  addFuns [(n',0)]
  addIndirection n (Var n')
  return n'

-- | Add a new indirection
addIndirection :: Name -> Expr -> TM ()
addIndirection n e = TM $ do
    write' $ "indirection: " ++ n ++ " := " ++ prettyCore e
    mem <- M.member n <$> gets boundNames
    when (mem) $ write' "warn: indirection already exists, overwriting"
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

-- | Looks up the constructors for a datatype
lookupConstructors :: Name -> TM [Name]
lookupConstructors c = TM $ (fromUnbound "lookupConstructors" c . M.lookup n)
                         <$> gets conFam

-- | Looks up an arity of a function or constructor
lookupArity :: Name -> TM Int
lookupArity n = TM $ (fromUnbound "lookupArity" n . M.lookup n)
                  <$> gets arities

-- | Looks up the projections for a constructor
lookupProj :: Name -> TM [FunName]
lookupProj n = TM $ (fmap FunName . fromUnbound "lookupProj" n . M.lookup n)
                 <$> gets conProj

-- | Make a pointer name of a name
makePtrName :: Name -> Name
makePtrName n = n ++ ".ptr"

-- | Make a pointer of a function name
makeFunPtrName :: FunName -> FunName
makeFunPtrName = FunName . makePtrName . funName

-- | Add functions/constructor name and arity.
addNameAndArity :: MonadState St m =>
                   (FunName -> Bound) -> [(Name,Int)] -> m ()
addNameAndArity mk funs = do
   modify boundNames (insertMany [(n,mk (FunName n))| (n,_) <- funs])
   modify arities (insertMany funs)

addTypes :: [(Name,Type)] -> TM ()
addTypes ts = TM $ do
  mapM_ (\(n,t) -> write' $ "addTypes: " ++ n ++ " :: " ++ show t) ts
  modify types (insertMany ts)

-- | Add functions name and arity
addFuns :: [(Name,Int)] -> TM ()
addFuns = TM . addNameAndArity FunVar

-- | Add a datatype's constructor given the arities
--   Projections are also generated, and added as functions
addCons :: [Decl] -> TM ()
addCons datadecls = TM $ do
     addNameAndArity ConVar (concat css)
     modify conProj (insertMany projs)
     modify datatypes (css ++)
     unTM (addFuns projfuns)
     unTM (mapM_ addTypes (map conTypes datadecls))
     modify conFam (insertMany fams)
  where
    css   = map conNameArity datadecls
    fams  = [ (n,map conName cs) | Data n _ cs <- datadecls ]
    projs = [ projName c | cs <- css, c <- cs]

    projfuns :: [(Name,Int)]
    projfuns = [ (pname,1)
               | cs <- css
               , c <- cs
               , pname <- snd (projName c)
               ]

    projName :: (Name,Int) -> (Name,[Name])
    projName (c,n) = (c,[c ++ "_" ++ show x  | x <- [0..n-1]])

-- | Mark a pointer as used
useFunPtr :: Name -> TM ()
useFunPtr fn = TM $ modify usedFunPtrs (S.insert fn)

-- | A list of nice variable names
varNames :: [String]
varNames = [1..] >>= flip replicateM "XYZWVU"

-- | Make a number of new variable names
makeVarNames :: Int -> [VarName]
makeVarNames n = take n (map VarName varNames)

-- | Fold the function app over the arguments
--
-- > appFold f [x,y,z] = app(app(app(f,x),y),z)
-- > appFold f []      = f
appFold :: Term -> [Term] -> Term
appFold = foldl (\f x -> T.Fun (FunName "app") [f,x])

-- | All FOL declarations from an environment and state
envStDecls :: TM [T.Decl]
envStDecls = TM $ do
  s <- get
  return $ projDecls (_conProj s) ++
           ptrDecls (_arities s) (_usedFunPtrs s) ++
           disjDecls (_datatypes s)

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
    datatypeDisj ctors = concat (zipWith constrDisj ctors'
                                                    (tail (tails ctors')))
      where ctors' = (bottomName,0) : ctors

    -- Make this constructor unequal to all the constructors in the list
    constrDisj :: (Name,Int) -> [(Name,Int)] -> [T.Decl]
    constrDisj x = map (disjunct x) . filter ((fst x /=) . fst)
                                   -- ^ avoid making bottom/=bottom

    -- Make two constructors disjunct
    disjunct :: (Name,Int) -> (Name,Int) -> T.Decl
    disjunct (c1,a1) (c2,a2) = T.Axiom ("disj" ++ c1 ++ c2)
       $ forall' (xs ++ ys) $ Fun (FunName c1) (map T.Var xs)
                             !=
                             Fun (FunName c2) (map T.Var ys)

      where (xs,ys) = splitAt a1 (makeVarNames (a1 + a2))

-- | Make projection declarations
projDecls :: Map Name [Name] -> [T.Decl]
projDecls = concatMap (uncurry mkDecl) . M.toList
  where
    mkDecl :: Name -> [Name] -> [T.Decl]
    mkDecl c ps = [ Axiom ("proj" ++ p) $ forall' xs $
                        Fun (FunName p) [Fun (FunName c) (map T.Var xs)]
                        === T.Var x
                  | x <- xs | p <- ps ]
      where arity = length ps
            xs    = makeVarNames arity

-- | Make pointer declarations
ptrDecls :: Map Name Int -> Set Name -> [T.Decl]
ptrDecls as = map mkDecl . S.toList
  where
    mkDecl fn = Axiom ("ptr" ++ fn)
              $ forall' xs
                $ appFold (Fun (FunName (makePtrName fn)) []) (map T.Var xs)
                  ===
                  Fun (FunName fn) (map T.Var xs)
      where arity = as M.! fn
            xs    = makeVarNames arity
