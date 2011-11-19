{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns, ParallelListComp #-}
module Language.HFOL.ToFOL.ToTPTP where

import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.Monad
import Language.HFOL.ToFOL.Constructors
import Language.HFOL.ToFOL.ProofDatatypes
import Language.HFOL.ToFOL.MakeProofs
import Language.HFOL.ToFOL.TranslateDecl

import Language.HFOL.FromHaskell.Names
import qualified Language.TPTP as T

import Control.Arrow ((&&&))
import Control.Applicative

import Data.List (partition)
import Data.Maybe (catMaybes)

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
                db      <- popDebug
                return (faxioms,extra,proofs,db)
  where
    (funAndProofDecls,datadecls',typedecls) = partitionDecls ds
    (proofdecls,fundecls) = partitionProofDecls funAndProofDecls
    funs  = map (declName &&& length . declArgs) fundecls
    types = map (declName &&& declType) typedecls
    datadecls = [Data "empty"  [] [Cons bottomName []]
                ,Data "Bool"   [] [Cons trueName [],Cons falseName []]
                ,Data unitName [] [Cons unitName []]
                ,Data listTypeName ["a"] [Cons nilName [],Cons consName [TyVar "a",TyCon listTypeName [TyVar "a"]]]
                ] ++
                [Data (tupleName n) (take n tyvars) [Cons (tupleName n) (map TyVar (take n tyvars))]
                | n <- [2..5] ]
                ++ filter (\d -> declName d `notElem` proofDatatypes) datadecls'
    tyvars = map return ['a'..]

partitionProofDecls :: [Decl] -> ([Decl],[Decl])
partitionProofDecls = partition isProofDecl
   where
       isProofDecl (Func fname _ (Expr e)) =
            fname `elem` proveFunctions || provable e
       isProofDecl _ = False

