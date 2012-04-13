{-# LANGUAGE RecordWildCards #-}
module Hip.Trans.MakeTheory where

import Hip.Trans.Theory
import Hip.Trans.Core
import Hip.Trans.Monad
import Hip.Trans.Constructors
import Hip.Trans.ProofDatatypes
import Hip.Trans.MakeProofs
import Hip.Trans.TranslateDecl
import Hip.Trans.NecessaryDefinitions
import Hip.Trans.Pretty
import Hip.Messages
import Hip.Util
import Hip.Params

import qualified Language.TPTP as T

import Control.Arrow ((&&&),(***),second,first)
import Control.Applicative

import Data.List (partition,nub,find)
import Data.Maybe (catMaybes,fromMaybe)
import Control.Monad

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)

import Data.Traversable (for)

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
    dataDecls = Data "Bool" []    [Cons trueName [],Cons falseName []]
              : Data "[]"   ["a"] [Cons "[]" [],Cons ":" [TyVar "a",TyCon "[]" [TyVar "a"]]]
              : filter (\d -> declName d `notElem` proofDatatypes) dataDecls'


etaExpand :: Expr -> Expr -> [Name] -> Type
          -> (Expr,Expr,[Name],Type)
etaExpand lhs rhs args ty =
  case unProp (resType ty) of
         -- Prop (a -> b) ~= a -> Prop b
         TyApp ts -> let extraTyVars = zip [ "x." ++ show x | x <- [0..] ]
                                           (init ts)
                     in (foldl app lhs (map (Var . fst) extraTyVars)
                        ,foldl app rhs (map (Var . fst) extraTyVars)
                        ,args ++ map fst extraTyVars
                        ,foldr tapp (TyCon "Prop" [last ts]) (argsTypes ty ++ init ts)
                        )
         _        -> (lhs,rhs,args,ty)

makeTheory :: Params -> [Decl] -> (Theory,[Prop],[Msg])
makeTheory params ds =
  let ProcessedDecls{..} = processDecls ds
      funs          = map (declName &&& length . declArgs) funDecls
      types         = map (declName &&& declType) typeDecls

      call_graph = declsToGraph ds

      recursiveFuns :: Set Name
      recursiveFuns = S.fromList [ name
                                 | d@(Func name args body) <- funDecls
                                 , recursive call_graph name
                                 ]

      (thy_functions,thy_msgs) = unzip $ flip map funDecls $ \fun_decl -> runTM params $ do
                                     let name = declName fun_decl
                                         (used_funs,used_datas)
                                            = iterateFCs call_graph (S.singleton name)
                                     addFuns funs
                                     addCons dataDecls
                                     addTypes types
                                     (_,tptp) <- translate fun_decl
                                     maybe_type <- lookupType name
                                     used_ptrs <- getUsedFunPtrs
                                     msgs <- popMsgs
                                     return (ThyFun { funcName       = name
                                                    , funcTPTP       = tptp
                                                    , funcPtrs       = used_ptrs
                                                    , funcFunDeps    = used_funs
                                                    , funcDataDeps   = used_datas
                                                    , funcType       = maybe_type
                                                    , funcDefinition = fun_decl
                                                    , funcRecursive  = name `S.member` recursiveFuns
                                                    }
                                            ,msgs)

      properties = catMaybes $ flip map proofDecls $ \proof_decl ->
                      case proof_decl of
                          Func prop_name args e -> do
                             (lhs,rhs) <- case e of
                                  Expr (App "proveBool" [lhs])             -> Just (lhs,Con "True" [])
                                  Expr (App "prove" [App "=:=" [lhs,rhs]]) -> Just (lhs,rhs)
                                  Expr (App "=:=" [lhs,rhs])               -> Just (lhs,rhs)
                                  _ -> Nothing
                             ty <- lookup prop_name types
                             let (lhs',rhs',args',ty') = etaExpand lhs rhs args ty
                             return (Prop { proplhs  = lhs'
                                          , proprhs  = rhs'
                                          , propVars = args'
                                          , propName = prop_name
                                          , propType = ty'
                                          , propRepr = prettyCore e
                                          , propQSTerms = error "MakeTheory.makeTheory.properties : propQSTerms does not exist for this property!"
                                          })
  in  (Theory thy_functions dataDecls (declsToGraph (funDecls ++ dataDecls))
      ,properties
      ,concat thy_msgs)

partitionProofDecls :: [Decl] -> ([Decl],[Decl])
partitionProofDecls = partition isProofDecl
   where
       isProofDecl (Func fname _ (Expr e)) =
            fname `elem` proveFunctions || provable e
       isProofDecl _ = False

  {-

dumpTPTP :: Params -> [Decl] -> ([(Decl,[T.Decl])],[T.Decl],[Msg])
dumpTPTP params ds = runTM params $ do
    addFuns funs
    addCons dataDecls
    addTypes types
    faxioms <- mapM translate funDecls
    extra   <- envStDecls
    db      <- popMsgs
    return (faxioms,extra,db)
  where
    ProcessedDecls{..} = processDecls ds
    funs  = map (declName &&& length . declArgs) funDecls
    types = map (declName &&& declType) typeDecls


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

-- These were added since StructuralInduction sometimes returns empty
-- parts because it overflowed the number allowed hyps or steps, and
-- this was inside the monad so this was the easiest fix, but yes
-- it's an ugly hack and I sorry I do not have more time for this
removeEmptyProperties :: [Property] -> [Property]
removeEmptyProperties = filter (not . null . propMatter)

removeEmptyParts :: Property -> Property
removeEmptyParts (Property n c parts)
  = Property n c (filter (not . null . snd . partMatter) parts)

prepareProofs :: Params -> [Decl] -> ([Property],[Msg])
prepareProofs params ds = first (removeEmptyProperties . map removeEmptyParts)
                        $ second ((extraDebug ++) . concat)
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
                    partsm    = makeProofDecls params fundecls recursiveFuns sigty d
                    (parts,dbg) = unzip $ flip map partsm $ \partm -> runTM params $ do
                        wdproof $ propName
                        addTypes types
                        addCons datadecls
                        part  <- partm
                        extra <- envStDecls
                        db    <- popMsgs
                        return (extendPart extra part,db)
                return $ (Property { propName   = propName
                                   , propCode   = prettyCore (funcBody d)
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

-}