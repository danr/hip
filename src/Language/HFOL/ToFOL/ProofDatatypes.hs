module Language.HFOL.ToFOL.ProofDatatypes where

import qualified Language.TPTP as T
import Language.HFOL.ToFOL.Core

proofDatatypes :: [Name]
proofDatatypes = ["Prop"]

proveFunctions :: [Name]
proveFunctions = ["prove","proveBool","given","givenBool"]

provable :: Expr -> Bool
provable (App f es) = f `elem` proveFunctions || any provable es
provable _          = False

data ProofDecl = ProofDecl Name [ProofType]
  deriving (Eq,Ord,Show)

data ProofType = Plain [T.Decl]
               | NegInduction [Name] [T.Decl]
               | Induction [Name] [IndPart]

  deriving (Eq,Ord,Show)

data IndPart = IndPart { indVarCon :: [Name]
                       , indDecls  :: [T.Decl]
                       }
  deriving (Eq,Ord,Show)