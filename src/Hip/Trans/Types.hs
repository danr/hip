module Types(finiteTy,keep,anyTypeAxiom,typeGuard,genTypePred) where

import Hip.Trans.Core
import Hip.Trans.Pretty
import Hip.Trans.ParserInternals
import Hip.Trans.StructuralInduction
import Hip.Trans.TyEnv hiding (VarName)
import Hip.Trans.Names

import qualified Language.TPTP as T
import Language.TPTP hiding (Decl,Var)

import Data.Char

import Control.Applicative
import Control.Monad

-- | Is a constructor with a type finite?
finiteCon :: Env -> [Type] -> Type -> Bool
finiteCon env tys t = not (any (`elem` tys) (argsTypes t))
                   && all (finiteTypeMut env tys) (argsTypes t)

-- | Is this type finite?
--
--   True  : Bool, (Bool,Bool), Ordering, Unit
--   False : a, [a], (a,Bool)
finiteTy :: Env -> Type -> Bool
finiteTy env ty = finiteTypeMut env [] ty

finiteTypeMut env tys ty@TyCon{} = case instantiate ty env of
    Just cons -> all (finiteCon env (ty:tys) . snd) cons
    Nothing   -> error $ "finiteTypeMut: " ++ show ty
finiteTypeMut _ _ _ = False -- Type variable or function space

-- | Should this type be kept? In other words, does it  contain
--   any subparts that are finite?
--
--   True  : Bool, [Bool], (Bool,a), [(Nat,Bool)]
--   False : [a], Nat
keep :: Env -> Type -> Bool
keep env ty@(TyCon _ ts) = finiteTy env ty || any (keep env) ts
keep env _               = False

testTypes = map parseType
   [ "Bool"
   , "Tree Bool"
   , "Tree a"
   , "List Bool"
   , "Unit"
   , "Maybe Bool"
   , "WrapList Bool"
   , "Nat"
   , "Z"
   , "Tup Bool Bool"
   , "Tup Unit Bool"
   , "Tup a Bool"
   , "Tup Bool (List a)"
   , "Either Bool Unit"
   , "Either Unit (List Unit)"
   , "Tup (Tup (Tup Bool Bool) (Either Bool Bool)) (Either Unit Bool)"
   , "Tup (Tup (Tup Bool Nat) (Either Bool Bool)) (Either Unit Bool)"
   ]

testFiniteTy,testKeep :: [(TypeName,Bool)]
testFiniteTy = map ((,) <$> show <*> finiteTy testEnv) testTypes
testKeep     = map ((,) <$> show <*> keep testEnv) testTypes

-- | Generates the type predicate for a type
--
--   Example
--
--     Ty([a],[])
--     Ty([a],x:xs) <-> (Ty(a,x) /\ Ty([a],xs))
--
--     Ty((a,b),(x,y)) <-> (Ty(a,x) /\ Ty(b,y))
genTypePred :: Env -> Type -> T.Decl
genTypePred env ty@(TyCon n as) = case instantiate ty env of
   Just cons -> genPred ty (map unTyVar as) cons
   Nothing   -> error $ "genTypePred, not found: " ++ show ty
genTypePred env ty = error $ "genTypePred, not on a type constructor: " ++ show ty

genPred :: Type -> [Name] -> [(Name,Type)] -> T.Decl
genPred ty tvs cons = Axiom "ty" (forall' (x : map quantName (tyVars ty))
                                          (rootFormula <=>
                                             foldr1 (\/) (map (uncurry genPredCon) cons)))
  where
     x  = VarName "R"
     xv = T.Var x

     rootFormula = tyRel (genType (resType ty)) xv

     genPredCon :: ConName -> Type -> T.Formula
     genPredCon con_name ty =
         exists' (map fst typedvars) $
            foldr (/\)
                  (xv === Fun (FunName con_name) (map (T.Var . fst) typedvars))
                  (map (\(v,t) -> tyRel (genType t) (T.Var v)) typedvars)
       where
         typedvars = makeVarNames (length (argsTypes ty)) `zip` argsTypes ty


infDomainAxiom :: Env -> Type -> Maybe T.Decl
infDomainAxiom env t = undefined

genType :: Type -> T.Term
genType (TyVar v)    = T.Var (quantName v)
genType (TyCon n ts) = Fun (FunName n) (map genType ts)
genType t@TyApp{}    = error $ "genType on function space: " ++ show t

anyTypeAxiom :: T.Decl
anyTypeAxiom = Axiom "anytype" $ forall' [x] (tyRel anyType xv)
  where
    x  = VarName "X"
    xv = T.Var x

typeGuard :: Env -> T.Term -> Type -> T.Formula -> T.Formula
typeGuard env tm ty phi | keep env ty = tyRel (genType (instAny env ty)) tm ==> phi
typeGuard env tm ty phi               = phi

instAny :: Env -> Type -> Type
instAny env t | not (keep env t) = TyVar anyTypeName
instAny env (TyCon n ts)         = TyCon n [ if isTyVar t then TyVar anyTypeName
                                                          else instAny env t
                                           | t <- ts ]


anyTypeName :: Name
anyTypeName = "any-type"

anyType :: T.Term
anyType = Fun (FunName anyTypeName) []

tyRel :: T.Term -> T.Term -> T.Formula
tyRel t1 t2 = Rel (RelName "ty") [t1,t2]

-- | A list of nice variable names
varNames :: [String]
varNames = [1..] >>= flip replicateM "XYZWVU"

-- | Make a number of new variable names
makeVarNames :: Int -> [T.VarName]
makeVarNames n = take n (map VarName varNames)

quantName :: Name -> T.VarName
quantName = VarName . map toUpper

