{-# LANGUAGE ViewPatterns #-}
module Autospec.Results where

import Autospec.ToFOL.ProofDatatypes

import Control.Applicative

type Problem = Principle String
type Res     = Principle Result

data Result = Theorem          -- ^ Theroem
            | Countersat       -- ^ Countersatisfiable
            | Timeout          -- ^ Timeout
            | Unknown String   -- ^ Unknown message from prover
            | FiniteTheorem    -- ^ This is a theorem for finitevalues
            | Inconsistent     -- ^ If we both have Theorem and Countersat
            | None             -- ^ No information when flattened
  deriving (Eq,Ord)

instance Show Result where
  show Theorem       = "Theorem"
  show Countersat    = "Countersatisfiable"
  show Timeout       = "Timeout"
  show (Unknown s)   = "??: " ++ s
  show FiniteTheorem = "Finite Theorem"
  show Inconsistent  = "INCONSISTENT"
  show None          = "None"

flattenRes :: Part Result -> Result
flattenRes (Part _ Theorem    FiniteSuccess) = FiniteTheorem
flattenRes (Part _ Timeout    InfiniteFail)  = FiniteTheorem
flattenRes (Part _ None       InfiniteFail)  = FiniteTheorem
flattenRes (Part _ Countersat EpicFail)      = Countersat
flattenRes (Part _ Countersat InfiniteFail)  = FiniteTheorem
flattenRes (Part _ Countersat Fail)          = None
flattenRes (Part _ r _)                      = r

isUnknown :: Result -> Bool
isUnknown (Unknown _) = True
isUnknown _           = False

combineRes :: [Result] -> Result
combineRes rs
   | all ((Theorem ==))                                 rs = Theorem
   | all ((||) <$> (Theorem ==) <*> (FiniteTheorem ==)) rs = FiniteTheorem
   | all (Countersat ==)                                rs = Countersat
   | any isUnknown                                      rs = Unknown ""
   | otherwise                                             = None

resFromParts :: [Part Result] -> Result
resFromParts = combineRes . map flattenRes

statusFromGroup :: [Res] -> Result
statusFromGroup (map principleDecor -> rs)
   | any (Countersat ==) rs && any (Theorem ==) rs = Inconsistent
   | any (Theorem ==) rs       = Theorem
   | any (FiniteTheorem ==) rs = FiniteTheorem
   | any (Countersat ==) rs    = Countersat
   | any isUnknown rs          = Unknown ""
   | otherwise                 = None
