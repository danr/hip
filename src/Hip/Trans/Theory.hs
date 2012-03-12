module Hip.Trans.Theory where

import Hip.Trans.Core
import Hip.Trans.ProofDatatypes
import Hip.Trans.Pretty
import Hip.Util
import qualified Language.TPTP as T
import Data.Set (Set)
import qualified Data.Set as S


data Theory = Theory { thyFuns  :: [ThyFun]
                     , thyDatas :: [Decl]
                     -- ^ Invariant: all are data declarations
                     }
  deriving (Eq,Ord,Show)

data ThyFun = ThyFun { funcName       :: Name
                     -- ^ The name of this function
                     , funcTPTP       :: [T.Decl]
                     -- ^ The generated TPTP theory for this function
                     , funcPtrs       :: [(Name,Int)]
                     -- ^ Function pointer this functions uses
                     , funcFunDeps    :: Set Name
                     -- ^ Func definitions this function uses, directly or indirectly
                     , funcDataDeps   :: Set Name
                     -- ^ Data types this function uses, directly or indirectly
                     , funcDefinition :: Decl
                     -- ^ The function definition
                     , funcRecursive  :: Bool
                     -- ^ Is this function recursive?
                     , funcType       :: Maybe Type
                     }
  deriving (Eq,Ord,Show)

data Prop = Prop { proplhs  :: Expr
                 , proprhs  :: Expr
                 , propVars :: [Name]
                 , propName :: Name
                 , propType :: Type
                 , propRepr :: String
                 }
  deriving (Eq,Ord,Show)

theoryFunDecls :: Theory -> [Decl]
theoryFunDecls = map funcDefinition . thyFuns

theoryRecFuns :: Theory -> Set Name
theoryRecFuns = S.fromList . map funcName . filter funcRecursive . thyFuns

theoryFunTPTP :: Theory -> [T.Decl]
theoryFunTPTP = concatMap funcTPTP . thyFuns

theoryUsedPtrs :: Theory -> [(Name,Int)]
theoryUsedPtrs = nubSorted . concatMap funcPtrs . thyFuns

theoryFiniteType :: Theory -> Type -> Bool
theoryFiniteType = undefined