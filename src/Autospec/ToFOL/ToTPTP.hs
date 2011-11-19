{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns, ParallelListComp #-}
module Autospec.ToFOL.ToTPTP where

import Autospec.ToFOL.Core
import Autospec.ToFOL.Monad
import Autospec.ToFOL.Constructors
import Autospec.ToFOL.ProofDatatypes
import Autospec.ToFOL.MakeProofs
import Autospec.ToFOL.TranslateDecl

import qualified Language.TPTP as T

import Control.Arrow ((&&&))
import Control.Applicative


import Data.List (partition)
import Data.Maybe (catMaybes)

import Autospec.ToFOL.NecessaryDefinitions
import Autospec.ToFOL.Pretty
import Control.Monad

-- | Translates a program to TPTP, with its debug output
--   First argument is if proof mode is on or not
toTPTP :: [Decl] -> ([(Decl,[T.Decl])],[T.Decl],[ProofDecl],Debug)
toTPTP ds = runTM $ do
                addFuns funs
                addCons datadecls
                addTypes types
                faxioms <- mapM translate fundecls
                proofs  <- catMaybes <$> mapM makeProofDecl proofdecls
                extra   <- envStDecls
                forM_ ds $ \d -> do write $ prettyCore d
                                    write . show . usedFC $ d
                db      <- popDebug
                return (faxioms,extra,proofs,db)
  where
    (funAndProofDecls,datadecls',typedecls) = partitionDecls ds
    (proofdecls,fundecls) = partitionProofDecls funAndProofDecls
    funs  = map (declName &&& length . declArgs) fundecls
    types = map (declName &&& declType) typedecls
    datadecls = Data "empty"  [] [Cons bottomName []]
              : Data "Bool"   [] [Cons trueName [],Cons falseName []]
              : filter (\d -> declName d `notElem` proofDatatypes) datadecls'

partitionProofDecls :: [Decl] -> ([Decl],[Decl])
partitionProofDecls = partition isProofDecl
   where
       isProofDecl (Func fname _ (Expr e)) =
            fname `elem` proveFunctions || provable e
       isProofDecl _ = False

