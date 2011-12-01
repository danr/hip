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
               | SimpleInduction       { indVar :: Name }
               | ApproxLemma
               | FixpointInduction     { fixFun :: Name }
  deriving (Eq,Ord)

data Failure = Fail | InfiniteFail
  deriving (Eq,Ord,Show)

instance Show ProofType where
  show Plain                 = "plain"
  show (SimpleInduction v)   = "simple induction on " ++ v
  show ApproxLemma           = "approximation lemma"
  show (FixpointInduction f) = "fix point induction on " ++ f

proofTypeFile :: ProofType -> String
proofTypeFile pt = case pt of
  Plain               -> "plain"
  SimpleInduction v   -> "simpleind" ++ v
  ApproxLemma         -> "approx"
  FixpointInduction f -> "fix" ++ f

data Principle k = Principle { principleName  :: Name
                             , principleType  :: ProofType
                             , principleDecor :: k
                             , principleParts :: [ProofPart]
                             }
  deriving (Eq,Ord,Show)

type ProofDecl = Principle [T.Decl]

data Part k = Part { partName  :: Name
                   , partDecor :: k
                   , partFail  :: Failure
                   }
  deriving (Eq,Ord,Show)

type ProofPart = Part [T.Decl]

proofPart :: Name -> [T.Decl] -> ProofPart
proofPart n d = ProofPart n d Fail

extendProofDecls :: [T.Decl] -> ProofDecl -> ProofDecl
extendProofDecls ts pd = pd { proofDecls = proofDecls pd ++ ts }

extendProofPart :: [T.Decl] -> ProofPart -> ProofPart
extendProofPart ts pp = pp { partDecls = partDecls pp ++ ts }

extendPrinciple :: Part k -> Principle k -> Principle k
extendPrinciple pt pd = pd { principleParts = principleParts ++ [pt] }