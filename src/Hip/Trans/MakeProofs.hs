{-# LANGUAGE RecordWildCards,NamedFieldPuns,TupleSections #-}
module Hip.Trans.MakeProofs where

import Hip.Trans.TranslateExpr
import Hip.Trans.TranslateDecl
import Hip.Trans.Core
import Hip.Trans.Constructors
import Hip.Trans.Monad
import Hip.Trans.Pretty
import Hip.Trans.ProofDatatypes
import Hip.Trans.NecessaryDefinitions
import Hip.Trans.FixpointInduction
import Hip.Trans.StructuralInduction
import Hip.Trans.Types
import Hip.Trans.TyEnv
import Hip.Trans.Theory
import Hip.Util (putEither,concatMapM)
import Hip.Messages
import Hip.Params

import Control.Applicative
import Control.Monad

import Data.Maybe (fromMaybe,mapMaybe)
import Control.Arrow ((&&&))

import Data.Set (Set)
import qualified Data.Set as S

type MakerM = HaltM

runMakerM = runHaltM

-- | Takes a theory, and prepares the invocations
--   for a property and adds the lemmas
theoryToInvocations :: Params -> Theory -> Prop -> [Prop] -> MakerM Property
theoryToInvocations params@(Params{..}) theory prop lemmas = do
    tr_lemmas <- sequence [ Lemma (propRepr lemma) (equals lemma) | lemma <- lemmas ]
    parts <- mapM (extendPart tr_lemmas) =<< prove params theory prop
    return $ Property { propName   = propName prop
                      , propCode   = propRepr prop
                      , propMatter = parts
                      }

equals :: Prop -> MakerM VarFormula
equals Prop{proplhs,proprhs,propVars} = do
    let vars = map fst propVars
    lhs <- trExpr proplhs
    rhs <- trExpr proprhs
    return (forall' vars (lhs === rhs))

prove :: Params -> Theory -> Prop -> MakerM [Part]
prove Params{methods} thy@Theory{..} prop lemmas =
    sequence [ plainProof | 'p' `elem` methods ]
  where
    plainProof :: MakerM Part
    plainProof = do
         equality <- equals prop
         let particle = Particle "plain" [Conjecture "plain" equality]
         return $ Part Plain (thyDataAxioms,thyDefAxioms,[particle])




