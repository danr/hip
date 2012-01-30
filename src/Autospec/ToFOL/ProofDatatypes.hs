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

data ProofMethod = Plain
                 | SimpleInduction         { indVar :: Name }
                 | ApproxLemma
                 | FixpointInduction       { fixFuns :: [Name] }
                 | StructuralInduction     { indVars :: [Name]
                                           , addBottom :: Bool
                                           , depth :: Int }
  deriving (Eq,Ord)

data Coverage = Infinite
              -- ^ Infinite and partial values
              | Finite
              -- ^ Finite and total values
  deriving (Eq,Ord,Show)

instance Show ProofMethod where
  show Plain                       = "plain"
  show (SimpleInduction v)         = "simple induction on " ++ v
  show ApproxLemma                 = "approximation lemma"
  show (FixpointInduction f)       = "fixed point induction on " ++ unwords f
  show (StructuralInduction vs b d) = concat [ "finite " | not b ] ++ "structural induction on " ++
                                      unwords vs ++ " depth " ++ show d

proofTypeFile :: ProofMethod -> String
proofTypeFile pt = case pt of
  Plain                      -> "plain"
  SimpleInduction v          -> "simpleind" ++ v
  ApproxLemma                -> "approx"
  FixpointInduction f        -> "fix" ++ concat f
  StructuralInduction vs b d -> concat [ "fin" | not b ] ++ "strind" ++ concat vs ++ show d

proofTypes :: [ProofMethod]
proofTypes = [Plain,SimpleInduction ""
             ,ApproxLemma
             ,FixpointInduction []
             ,StructuralInduction [] True 0
             ]


liberalEq :: ProofMethod -> ProofMethod -> Bool
liberalEq Plain Plain                                         = True
liberalEq SimpleInduction{} SimpleInduction{}                 = True
liberalEq ApproxLemma ApproxLemma                             = True
liberalEq FixpointInduction{} FixpointInduction{}             = True
liberalEq StructuralInduction{} StructuralInduction{}         = True
liberalEq _ _                                                 = False

liberalShow :: ProofMethod -> String
liberalShow Plain                     = "plain"
liberalShow SimpleInduction{}         = "simple induction"
liberalShow ApproxLemma               = "approximation lemma"
liberalShow FixpointInduction{}       = "fixed point induction"
liberalShow StructuralInduction{}     = "structural induction"

latexShow :: ProofMethod -> String
latexShow Plain                     = "plain"
latexShow SimpleInduction{}         = "simple ind"
latexShow ApproxLemma               = "approx"
latexShow FixpointInduction{}       = "fixpoint ind"
latexShow StructuralInduction{}     = "struct ind"

data Part = Part { partProperty  :: Name
                 , partCode      :: String
                 , partMethod    :: ProofMethod
                 , partTheory    :: [T.Decl]
                 , partParticles :: [Particle]
                 , partCoverage  :: Coverage
                 }
  deriving (Eq,Ord,Show)

data Particle = Particle { particleDesc   :: String
                         , particleAxioms :: [T.Decl]
                         }
  deriving (Eq,Ord,Show)

{-
type ProofPart = Part [T.Decl]

proofDecl :: Name -> ProofMethod -> [T.Decl] -> String -> [ProofPart] -> ProofDecl
proofDecl = Principle

proofPart :: Name -> [T.Decl] -> ProofPart
proofPart n d = Part n d Fail

extendProofDecls :: [T.Decl] -> ProofDecl -> ProofDecl
extendProofDecls ts pd = pd { principleDecor = principleDecor pd ++ ts }

extendProofPart :: [T.Decl] -> ProofPart -> ProofPart
extendProofPart ts pp = pp { partDecor = partDecor pp ++ ts }

extendPrinciple :: Part k -> Principle k -> Principle k
extendPrinciple pt pd = pd { principleParts = principleParts pd ++ [pt] }
-}

extendParticle :: [T.Decl] -> Particle -> Particle
extendParticle axioms p = p { particleAxioms = particleAxioms p ++ axioms }