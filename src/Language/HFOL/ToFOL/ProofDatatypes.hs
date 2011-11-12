module Language.HFOL.ToFOL.ProofDatatypes where

import qualified Language.TPTP as T
import Language.HFOL.ToFOL.Core

proofDatatypes :: [[(Name,Int)]]
proofDatatypes = [[("Prove",1)]]

proveFunctions :: [Name]
proveFunctions = ["prove","proveBool","given","givenBool"]

provable :: Expr -> Bool
provable (App f es) = f `elem` proveFunctions || any provable es
provable _          = False

data ProofDecl = ProofDecl Name ProofType
  deriving (Eq,Ord,Show)

data ProofType = Plain [T.Decl]
               | Induction [Name] [[T.Decl]]
  deriving (Eq,Ord,Show)
