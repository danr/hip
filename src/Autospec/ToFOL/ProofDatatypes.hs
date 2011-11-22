module Autospec.ToFOL.ProofDatatypes where

import qualified Language.TPTP as T
import Autospec.ToFOL.Core

proofDatatypes :: [Name]
proofDatatypes = ["Prop"]

proveFunctions :: [Name]
proveFunctions = ["prove","proveBool","given","givenBool","=:="]

provable :: Expr -> Bool
provable (App f es) = f `elem` proveFunctions || any provable es
provable _          = False

data ProofType = Plain
               | FiniteSimpleInduction { indVar :: Name }
               | SimpleInduction       { indVar :: Name }
               | ApproxLemma
               | FixpointInduction
  deriving (Eq,Ord)

instance Show ProofType where
  show Plain                     = "Plain"
  show (FiniteSimpleInduction v) = "finite simple induction on " ++ v
  show (SimpleInduction v)       = "simple induction on " ++ v
  show ApproxLemma               = "approximation lemma"
  show FixpointInduction         = "fix point induction"

proofTypeFile :: ProofType -> String
proofTypeFile pt = case pt of
  Plain                   -> "plain"
  FiniteSimpleInduction v -> "finitesimplind" ++ v
  SimpleInduction v       -> "simpleind" ++ v
  ApproxLemma             -> "approx"
  FixpointInduction       -> "fix"

data ProofDecl = ProofDecl { proofName  :: Name
                           , proofType  :: ProofType
                           , proofDecls :: [T.Decl]
                           , proofParts :: [ProofPart]
                           }
  deriving (Eq,Ord,Show)

data ProofPart = ProofPart { partName  :: Name
                           , partDecls ::[T.Decl]
                           }
  deriving (Eq,Ord,Show)

extendProofDecls :: [T.Decl] -> ProofDecl -> ProofDecl
extendProofDecls ts pd = pd { proofDecls = proofDecls pd ++ ts }