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
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)

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

prepareProofs :: [Decl] -> ([Property],[Msg])
prepareProofs ds = second ((extraDebug ++) . concat)
                 $ unzip (concatMap processDecl proofDecls)
  where
    extraDebug = [dbproofMsg $ "Recursive functions: " ++ show recursiveFuns]

    processDecl :: Decl -> [(Property,[Msg])]
    processDecl d
      | declName d `elem` proveFunctions = []
      | otherwise =
          let propName = declName d
              mty = declType <$> find ((propName ==) . declName) typeDecls
          in case mty of
              Nothing -> []
              Just sigty -> do
                let (fsd,csd)    = usedFC d
                    typesFromSig = getTypes sigty
                    (fs,cs')  = compIterateFCs (fsd S.\\ S.fromList proveFunctions)
                    cs        = S.insert bottomName $ csd `S.union` cs'
                    datadecls = filterDatas typesFromSig cs dataDecls
                    fundecls  = filterFuns  fs funDecls
                    partsm    = makeProofDecls fundecls recursiveFuns sigty d
                    (parts,dbg) = unzip $ flip map partsm $ \partm -> runTM $ do
                        dbproof $ propName
                        addTypes types
                        addCons datadecls
                        part  <- partm
                        extra <- envStDecls
                        db    <- popDebug
                        return (extendPart extra part,db)
                return $ (Property { propName  = propName
                                   , propCode  = prettyCore (funcBody d)
                                   , propMatter = parts
                                   },concat dbg)

    ProcessedDecls{..} = processDecls ds
    types = map (declName &&& declType) typeDecls

    compIterateFCs :: Set Name -> (Set Name,Set Name)
    compIterateFCs = iterateFCs funDecls

    usedFCmap :: Map Name (Set Name,Set Name)
    usedFCmap = M.fromList [ (declName d,usedFC d) | d <- funDecls ]

    recursiveFuns :: Set Name
    recursiveFuns = S.fromList
        [ name
        | d@(Func name args body) <- funDecls
        , let namecalls = fst (usedFCmap M.! name)
              -- ^ Which functions this function calls
              theycall  = fst (compIterateFCs namecalls)
              -- ^ All functions they call. If name is member
              --   there then there is a mutual recursion
        , selfRecursive d || name `S.member` theycall
        ]

