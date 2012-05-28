module Hip.Trans.Theory where

import Hip.Trans.Core
import Hip.Trans.ProofDatatypes hiding (propName)
import Hip.Trans.Pretty
import Hip.Trans.TyEnv
import Hip.Trans.NecessaryDefinitions
import Hip.Util

import Halt.FOL.Abstract

import Hip.StructuralInduction

import CoreSyn
import Var
import TysWiredIn

import qualified Test.QuickSpec.Term as QST

import Control.Arrow ((&&&),first)

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph
import Data.Tree
import Data.Maybe


data Theory = Theory { thyDataAxioms :: [AxClause]
                     , thyDefAxioms  :: [VarClause]
                     , thyTyEnv      :: TyEnv Var Type
                     }


data Prop = Prop { proplhs  :: CoreExpr
                 , proprhs  :: CoreExpr
                 , propVars :: [(Var,Type)]
                 , propName :: Var
                 , propRepr :: String
                 , propQSTerms :: {- Maybe -} (QST.Term QST.Symbol,QST.Term QST.Symbol)
                 }
  deriving (Eq,Ord,Show)

inconsistentProp :: Prop
inconsistentProp = Prop { proplhs  = con trueDataConId
                        , proprhs  = con falseDataConId
                        , propVars = []
                        , propName = color Red "inconsistencyCheck"
                        , propType = boolTy
                        , propRepr = "inconsistecy check: this should never be provable"
                        , propQSTerms = error "propQSTerms: inconsistentProp"
                        }

thyFiniteType :: Theory -> Type -> Bool
thyFiniteType = error "thyFiniteType: unimplemented"

