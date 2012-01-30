{-# LANGUAGE RecordWildCards #-}
module Autospec.ResultDatatypes where

import Autospec.Util
import Data.Maybe
import Data.Function

-- Result from a prover invocation --------------------------------------------

data ProverResult = Success { successTime :: Int }
                  -- ^ Success: Theorem or Countersatisfiable
                  | Failure
                  -- ^ Fialure: Satisfiable etc, and timeouts or skipped
                  | Unknown String
                  -- ^ Unreckognized output. For debugging

success :: ProverResult -> Bool
success Success{} = True
success _         = False

unknown :: ProverResult -> Bool
unknown Unknown{} = True
unknown _         = False

flattenProverResults :: [ProverResult] -> ProverResult
flattenProverResults xs
    | all success xs = Success (avgList (map successTime xs))
    | otherwise      = fromMaybe Failure (listToMaybe (filter unknown xs))

disjoinProverResults :: [ProverResult] -> ProverResult
disjoinProverResults = unlist Failure (Success . avgList . map successTime)
                     . filter success

instance Eq ProverResult where
  (==) = (==) `on` success

instance Show ProverResult where
  show (Success{..}) = "Success (" ++ show successTime ++ "ms)"
  show Failure     = "Failure"
  show (Unknown s) = "Unknown: " ++ show s

-- Result for an entire property or a proof part ------------------------------

data PropResult = Theorem | FiniteTheorem | None
  deriving (Eq,Ord,Show,Enum,Bounded)

latexResult :: PropResult -> String
latexResult Theorem       = "$\\checkmark_{\\infty}$"
latexResult FiniteTheorem = "$\\checkmark_{\\mathrm{fin}}$"
latexResult None          = ""

results :: [PropResult]
results = [minBound..maxBound]


