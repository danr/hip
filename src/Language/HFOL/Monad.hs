{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.HFOL.Monad
       (TM()
       ,runTM
       ,write
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

import Language.HFOL.Core
import Language.HFOL.Pretty
import Language.HFOL.Bottom
import Language.HFOL.Util (withPrevious)

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)
import Language.TPTP
import Language.TPTP.Pretty

import Control.Applicative
import Control.Monad
import Control.Monad.RWS

import Data.Maybe
import Data.List

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

-- | The TM monad.
--
--   The reader and state capabilities are kept abstract
newtype TM a = TM { unTM :: RWS Env [String] St a }
  deriving (Functor,Applicative,Monad)

-- | Runs a computation in an empty environment, with an empty state.
--   The computation's result is returned with the updated state.
runTM :: TM a -> (a,[String])
runTM (TM m) = evalRWS m emptyEnv emptySt

-- | Writes a debug message
write :: String -> TM ()
write = TM . tell . return

data Env = Env { arities    :: Map Name Int
                 -- ^ Arity of functions and constructors
               , conProj    :: Map Name [Name]
                 -- ^ Projection functions for constructors
               , conFam     :: Map Name [Name]
                 -- ^ The other constructors for a given constructor
               , datatypes  :: [[(Name,Int)]]
                 -- ^ The datatypes in the program
               }

data St = St { usedFunPtrs :: Set Name
               -- ^ Which functions we need to produce ptr conversions for
             , boundNames :: Map Name Bound
               -- ^ TPTP name of functions and constructors and quantified variables
             , quantified :: Set VarName
               -- ^ Variables to quantify over
             , namesupply :: [VarName]
               -- ^ Supply of variables
             }

data Bound = QuantVar    { quantVar  :: VarName }
           | FunVar      { boundName :: FunName }
           | ConVar      { boundName :: FunName }
           | Indirection { indExpr   :: Expr    }
  deriving(Eq,Ord,Show)

locally :: TM a -> TM a
locally (TM m) = TM $ do
  boundNames' <- gets boundNames
  r <- m
  modify $ \s -> s { boundNames = boundNames' , quantified = S.empty }
  return r

boundCon :: Bound -> Bool
boundCon (ConVar _) = True
boundCon _          = False

-- | The empty environment
emptyEnv :: Env
emptyEnv = Env M.empty M.empty M.empty []

-- | The empty state
emptySt :: St
emptySt = St S.empty M.empty S.empty [ T.VarName ('X' : show x) | x <- [0..] ]

-- | Insert /n/ elements to a map of /m/ elements
--
--   /O(n * log(m+n))/
insertMany :: Ord k => [(k,v)] -> Map k v -> Map k v
insertMany kvs m = foldr (uncurry M.insert) m kvs

-- | Looks up if a name is a variable or a function/constructor
lookupName :: Name -> TM Bound
lookupName n = TM $ do
    mn <- gets (M.lookup n . boundNames)
    case mn of
      Just b  -> return b
      Nothing -> do -- Variable is unbound, quantify over it
        q <- gets (head . namesupply)
        let qv = QuantVar q
        tell $ ["New quantified variable " ++ show q ++ " for " ++ n]
        modify $ \s -> s { boundNames = M.insert n qv (boundNames s)
                         , namesupply = tail (namesupply s)
                         , quantified = S.insert q (quantified s)
                         }
        return qv

addIndirection :: Name -> Expr -> TM ()
addIndirection n e = do
    write $ "indirection: " ++ n ++ " := " ++ prettyCore e
    TM $ modify $ \s -> s
          { boundNames = M.insert n (Indirection e) (boundNames s) }

popQuantified :: TM [VarName]
popQuantified = TM $ do
  qs <- gets (S.toList . quantified)
  modify $ \s -> s { quantified = S.empty }
  return qs

-- | Looks up an arity of a function or constructor
lookupArity :: Name -> TM Int
lookupArity n = TM $ asks (fromMaybe (error $ "lookupArity, unbound: " ++ n)
                          . M.lookup n . arities)

-- | Looks up the projections for a constructor
lookupProj :: Name -> TM [FunName]
lookupProj n = TM $ asks ( map FunName
                         . fromMaybe (error $ "lookupProj, unbound: " ++ n)
                         . M.lookup n . conProj)

-- | Binds the names to quantified variables inside the action
bindNames :: [Name] -> ([VarName] -> TM a) -> TM a
bindNames ns vm = TM $ do
    bnames <- gets boundNames
    let ns' = filter (`M.notMember` bnames) ns
        n = length ns'
    namesupply' <- gets namesupply
    let vs   = take n (namesupply')
        TM m = vm vs
    boundNames' <- gets boundNames
    modify $ \s -> s { boundNames =
                          insertMany (zipWith (\n v -> (n,QuantVar v)) ns' vs)
                                     boundNames'
                     , namesupply = drop n namesupply' }
    r <- m
    modify $ \s -> s { boundNames = boundNames'
                     , namesupply = namesupply'}
    return r

-- | Bind all variables in a pattern
bindPattern :: Pattern -> ([VarName] -> TM a) -> TM a
bindPattern p m = bindNames (fv p) m
  where
    fv (PVar x)    = return x
    fv (PCon c xs) = concatMap fv xs

-- | Make a pointer name of a name
makePtrName :: Name -> Name
makePtrName n = n ++ "_ptr"

-- | Make a pointer of a function name
makeFunPtrName :: FunName -> FunName
makeFunPtrName = FunName . makePtrName . funName

-- | Bind names that are functions or constructors
bindFunVars :: [Name] -> (FunName -> Bound) -> TM ()
bindFunVars ns mk = TM $ modify $ \s -> s
   { boundNames = insertMany [(n,mk (FunName n))| n <- ns] (boundNames s) }

addArities :: [(Name,Int)] -> TM a -> TM a
addArities funs (TM m) = TM $ flip local m $ \e -> e
                                       { arities = insertMany funs (arities e) }

-- | Add functions arities and name. This also works for constructors
addFuns :: [(Name,Int)] -> TM a -> TM a
addFuns funs m = do bindFunVars (map fst funs) FunVar
                    addArities funs m

-- | Add a datatype's constructor given the arities
--   Projections are also generated
addCons :: [[(Name,Int)]] -> TM a -> TM a
addCons css (TM m) = do
  bindFunVars cons ConVar
  addArities (concat css) $ TM $ flip local m $ \e -> e
      { conFam    = insertMany fams  (conFam e)
      , conProj   = insertMany projs (conProj e)
      , datatypes = css ++ datatypes e
      }
  where
    cons  = [ c          | cs <- css, (c,_) <- cs ]
    fams  = [ (c,cs')    | cs <- css, let cs' = map fst cs, c <- cs']
    projs = [ projName c | cs <- css, c <- cs]

    projName :: (Name,Int) -> (Name,[Name])
    projName (c,n) = (c,["proj" ++ show x ++ c | x <- [0..n-1]])

-- | Mark a pointer as used
useFunPtr :: Name -> TM ()
useFunPtr fn = TM $ modify $ \s -> s { usedFunPtrs = S.insert fn (usedFunPtrs s) }

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
  e <- ask
  s <- get
  return (projDecls (conProj e) ++
          ptrDecls (arities e) (usedFunPtrs s) ++
          disjDecls (datatypes e) )

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
    mkDecl c ps = zipWith (\x p -> T.Axiom ("axiom" ++ p)
                                 $ T.Forall xs $ T.EqOp
                                      (T.Fun (T.FunName p)
                                         [T.Fun (T.FunName c) (map T.Var xs)])
                                      (T.:==)
                                      (T.Var x))
                          xs ps
      where arity = length ps
            xs    = makeVarNames arity

-- | Make pointer declarations
ptrDecls :: Map Name Int -> Set Name -> [T.Decl]
ptrDecls arities = map mkDecl . S.toList
  where
    mkDecl fn = T.Axiom ("ptr" ++ fn)
              $ T.Forall xs
                $ T.EqOp (appFold (T.Var (T.VarName (makePtrName fn)))
                                   (map T.Var xs))
                         (T.:==)
                         (T.Fun (T.FunName fn) (map T.Var xs))
      where arity = arities M.! fn
            xs    = makeVarNames arity
