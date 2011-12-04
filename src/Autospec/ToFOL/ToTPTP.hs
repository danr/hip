{-# LANGUAGE RecordWildCards #-}
module Autospec.ToFOL.ToTPTP where

import Autospec.ToFOL.Core
import Autospec.ToFOL.Monad
import Autospec.ToFOL.Constructors
import Autospec.ToFOL.ProofDatatypes
import Autospec.ToFOL.MakeProofs
import Autospec.ToFOL.TranslateDecl
import Autospec.ToFOL.NecessaryDefinitions
import Autospec.ToFOL.Pretty
import Autospec.Messages
import Autospec.Util

import qualified Language.TPTP as T

import Control.Arrow ((&&&),(***),second)
import Control.Applicative

import Data.List (partition,nub,find)
import Data.Maybe (catMaybes,fromMaybe)
import Control.Monad

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)

data ProcessedDecls = ProcessedDecls { proofDecls :: [Decl]
                                     , funDecls   :: [Decl]
                                     , dataDecls  :: [Decl]
                                     , typeDecls  :: [Decl]
                                     }

processDecls :: [Decl] -> ProcessedDecls
processDecls ds = ProcessedDecls{..}
  where
    (funAndProofDecls,dataDecls',typeDecls) = partitionDecls ds
    (proofDecls,funDecls) = partitionProofDecls funAndProofDecls
    dataDecls = Data "empty"  [] [Cons bottomName []]
              : Data "Bool"   [] [Cons trueName [],Cons falseName []]
              : filter (\d -> declName d `notElem` proofDatatypes) dataDecls'

dumpTPTP :: [Decl] -> ([(Decl,[T.Decl])],[T.Decl],[Msg])
dumpTPTP ds = runTM $ do
    addFuns funs
    addCons dataDecls
    addTypes types
    faxioms <- mapM translate funDecls
    extra   <- envStDecls
    db      <- popDebug
    return (faxioms,extra,db)
  where
    ProcessedDecls{..} = processDecls ds
    funs  = map (declName &&& length . declArgs) funDecls
    types = map (declName &&& declType) typeDecls

partitionProofDecls :: [Decl] -> ([Decl],[Decl])
partitionProofDecls = partition isProofDecl
   where
       isProofDecl (Func fname _ (Expr e)) =
            fname `elem` proveFunctions || provable e
       isProofDecl _ = False

getTypes :: Type -> [Name]
getTypes ty  = case ty of
                  TyApp ts   -> concatMap getTypes ts
                  TyCon t ts -> t : concatMap getTypes ts
                  TyVar _    -> []

filterDatas :: [Name] -> Set Name -> [Decl] -> [Decl]
filterDatas typesFromSig cs =
    filter (\d -> any ((`S.member` cs) . conName) (dataCons d) ||
                  declName d `elem` typesFromSig)

filterFuns :: Set Name -> [Decl] -> [Decl]
filterFuns fs = filter ((`S.member` fs) . declName)

prepareProofs :: [Decl] -> ([ProofDecl],[Msg])
prepareProofs ds = second concat $ unzip (concatMap processDecl proofDecls)
  where
    processDecl :: Decl -> [(ProofDecl,[Msg])]
    processDecl d
      | declName d `elem` proveFunctions = []
      | otherwise =
          let fname = declName d
              mty = declType <$> find ((fname ==) . declName) typeDecls
          in case mty of
              Nothing -> []
              Just sigty ->
                let (fsd,csd)    = usedFC d
                    typesFromSig = getTypes sigty
                    (fs,cs')  = iterateFCs (fsd S.\\ S.fromList proveFunctions)
                    cs        = S.insert bottomName $ csd `S.union` cs'
                    datadecls = filterDatas typesFromSig cs dataDecls
                    fundecls  = filterFuns  fs funDecls
                    pdms      = makeProofDecls fundecls recursiveFuns sigty d
                in  flip map pdms $ \pdm -> runTM $ do
                        dbproof $ "Recursive functions: " ++ show recursiveFuns
                        addTypes types
                        addCons datadecls
                        pd    <- pdm
                        extra <- envStDecls
                        db    <- popDebug
                        return (extendProofDecls extra pd,db)

    ProcessedDecls{..} = processDecls ds
    types = map (declName &&& declType) typeDecls

    usedFCmap :: Map Name (Set Name,Set Name)
    usedFCmap = M.fromList [ (declName d,usedFC d) | d <- funDecls ]

    iterateFCs :: Set Name -> (Set Name,Set Name)
    iterateFCs fs | S.null newfs = (fs,cs)
                  | otherwise    = iterateFCs (fs `S.union` fs')
        -- Get the new functions from here
        where fs',cs :: Set Name
              (fs',cs) = (S.unions *** S.unions)
                         (unzip (map safeLookup (S.toList fs)))
              newfs = fs' S.\\ fs

    recursiveFuns :: Set Name
    recursiveFuns = S.fromList
        [ name
        | d@(Func name args body) <- funDecls
        , let namecalls = fst (usedFCmap M.! name)
              -- ^ Which functions this function calls
              theycall  = fst (iterateFCs namecalls)
              -- ^ All functions they call. If name is member
              --   there then there is a mutual recursion
        , selfRecursive d || name `S.member` theycall
        ]

    safeLookup :: Name -> (Set Name,Set Name)
    safeLookup f = fromMaybe (S.empty,S.empty) (M.lookup f usedFCmap)

