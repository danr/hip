{-# LANGUAGE RecordWildCards #-}
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
import Hip.Trans.StructuralInduction hiding (VarName,ConName)
import Hip.Trans.Theory
import Hip.Util (putEither,concatMapM)
import Hip.Messages
import Hip.Params

import Language.TPTP hiding (Decl,Var,VarName,declName)
import Language.TPTP.Pretty
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

import Data.Maybe (fromMaybe)
import Control.Arrow ((&&&))

import Data.Set (Set)
import qualified Data.Set as S

powerset :: [a] -> [[a]]
powerset = init . filterM (const [True,False])

unProp :: Type -> Type
unProp (TyCon _ [t]) = t
unProp t             = t

makeProofDecls :: Params -> Theory -> Prop -> [Prop] -> [TM Part]
makeProofDecls params theory prop@(Prop{..}) lemmas =
    let typedVars = case propType of TyApp ts -> zip propVars ts
                                     _        -> []

        resTy     = unProp (resType propType)

        fundecls  = theoryFunDecls theory

        recfuns   = theoryRecFuns theory

    in  case resTy of
           -- Prop (a -> b) ~= a -> Prop b
           TyApp ts -> let extraTyVars = zip [ "x." ++ show x | x <- [0..] ]
                                             (init ts)
                       in  prove params fundecls recfuns
                                 (last ts)
                                 propName
                                 (typedVars ++ extraTyVars)
                                 (foldl app proplhs (map (Var . fst) extraTyVars))
                                 (foldl app proprhs (map (Var . fst) extraTyVars))
           _        -> prove params fundecls recfuns resTy propName
                             typedVars proplhs proprhs

type Rec = Bool

type VarName = Name
type ConName = Name
type TyName  = Name
type SkolemName = Name
type LR a = Either a a

prove :: Params
      -- ^ The parameters to the program
      -> [Decl]
      -- ^ The function definitions in the file. The reason why this is
      --   here is because fixpoint induction needs to change some definitions
      -> Set Name
      -- ^ Which functions are recursive. Needed for fixpoint induction
      -> Type
      -- ^ The result type of the property
      -> Name
      -- ^ Name of the property
      -> [(Name,Type)]
      -- ^ Arguments together with type
      -> Expr
      -- ^ LHS
      -> Expr
      -- ^ RHS
      -> [TM Part]
      -- ^ Resulting instructions how to do proof declarations for this
prove params@(Params{..}) fundecls recfuns resTy fname typedVars lhs rhs =
    let indargs :: [(Name,Type)]
        indargs = filter (concreteType . snd) typedVars
        powset :: [[(Name,Type)]]
        powset = powerset indargs
    in  concat $ [ plainProof                                  | 'p' `elem` methods ]
--              ++ [ proofByFixpointInduction                    | 'f' `elem` methods ]
--              ++ [ proofByApproxLemma                          | 'a' `elem` methods ]
--              ++ [ map (proofByStructInd True  d)
--                       (filter ((<=indargs) .  length) powset) | d <- [1..inddepth], 's' `elem` methods ]
              ++ [ map (proofByStructInd False d)
                       (filter ((<=indvars) .  length) powset)
                 | d <- [1..inddepth], 'i' `elem` methods ]

  where
    accompanyParts :: ProofMethod -> Coverage -> TM [Particle] -> TM Part
    accompanyParts prooftype coverage partsm = do
        let funs = map (declName &&& length . declArgs) fundecls
--        addFuns funs
--        theory <- concatMapM (fmap snd . translate) fundecls
        parts  <- partsm
        return $ Part { partMethod     = prooftype
                      , partCoverage   = coverage
                      , partMatter     = ([],parts)
                      }


    accompanyPartsWithDecls :: ProofMethod
                            -> Coverage
                            -> [([Decl],TM [Particle])]
                            -> TM Part
    accompanyPartsWithDecls prooftype coverage tup = do
         parts <- flip concatMapM tup $ \(fundecls',partm) -> do
            let funs = map (declName &&& length . declArgs) fundecls'
            addFuns funs
            locally $ do
                part   <- partm
                theory <- concatMapM (fmap snd . translate) fundecls'
                return $ map (extendParticle theory) part
         return $ Part { partMethod     = prooftype
                       , partCoverage   = coverage
                       , partMatter     = ([],parts)
                       }

    proofByStructInd :: Bool -> Int -> [(Name,Type)] -> TM Part
    proofByStructInd addBottom d ns = accompanyParts
      (StructuralInduction (map fst ns) addBottom d)
      (if addBottom then Infinite else Finite) $ do
        env <- getEnv addBottom
        let parts = structuralInduction ns env d
        if length parts > 0 && (length parts <= indsteps || indsteps == 0)
          then forM parts $ \(IndPart hyps conj vars) -> locally $ do
--                  forM vars $ \v -> addIndirection v (Var v)
                  addFuns (zip vars (repeat 0))
                  let hyps' | indhyps == 0 = hyps
                            | otherwise    = take indhyps hyps
                  phyps <- mapM instP hyps'
                  pconj <- instP conj
                  return $ Particle { particleDesc   = unwords vars
                                    , particleMatter = Conjecture "conj" pconj :
                                                       [ Axiom "hyp" phyp | phyp <- phyps ]
                                    }
          else return []
      where
        instP :: [Expr] -> TM T.Formula
        instP es = locally $ do
            zipWithM addIndirection (map fst ns) es
            instantiateP []


    approxSteps :: TM (Formula,Formula,[T.Decl])
    approxSteps = do
        let f = "a.f"
        addFuns [(f,1)]
        (approx,approxTheory) <- approximate f resTy
        hyp <- locally $ do
                  lhs' <- translateExpr (App f [lhs])
                  rhs' <- translateExpr (App f [rhs])
                  forallUnbound (lhs' === rhs')
        step <- locally $ do
                  lhs' <- translateExpr (App approx [lhs])
                  rhs' <- translateExpr (App approx [rhs])
                  forallUnbound (lhs' === rhs')
        return (hyp,step,approxTheory)

    -- Returns in the List monad instead of the Maybe monad
    proofByApproxLemma :: [TM Part]
    proofByApproxLemma
       | concreteType resTy =
             [accompanyParts ApproxLemma Infinite $ do
                   (hyp,step,approxAxioms) <- approxSteps
                   return $ [Particle { particleDesc   = "step"
                                      , particleMatter = Axiom "approxhyp" hyp
                                                       : Conjecture "approxstep" step
                                                       : approxAxioms
                                      }]
             ]
       | otherwise = []

    plainProof :: [TM Part]
    plainProof
        | any (concreteType . snd) typedVars = []
        | otherwise =
            return $ accompanyParts Plain Infinite $ do
                p <- instantiateP []
                return $ [ Particle "plain" [Conjecture "plain" p] ]


    instantiateP :: [(VarName,VarName)] -> TM T.Formula
    instantiateP binds = locally $ do
        lhs' <- translateExpr (substVars binds lhs)
        rhs' <- translateExpr (substVars binds rhs)
        forallUnbound (lhs' === rhs')

    proofByFixpointInduction :: [TM Part]
    proofByFixpointInduction = concatMap
                                   instantiateFixProof
                                   ((if fpimax /= 0 then take fpimax else id)
                                    (proofByFixpoint fundecls recfuns lhs rhs))
      where
        instantiateEq :: (Expr,Expr) -> TM T.Formula
        instantiateEq (l,r) = locally $ do
            l' <- translateExpr l
            r' <- translateExpr r
            forallUnbound (l' === r')

        addFunsFromDecls ds = sequence_
           [ addFuns [(f,length as)] | Func f as _ <- ds ]

        addUnrecFunsFromDecls ds fixedFuns = sequence_
           [ addFuns [(f ++ unRec,length as)]
           | Func f as _ <- ds
           , f `elem` fixedFuns ]

        instantiateFixProof :: FixProof -> [TM Part]
        instantiateFixProof fp@(FixProof {..}) =
            [ accompanyPartsWithDecls (FixpointInduction fixedFuns) Infinite
                 [(baseDecls,baseAxioms)
                 ,(stepDecls,stepAxioms)]
            ]
          where
             baseAxioms = do
                 wdproof $ show fp
                 addFunsFromDecls baseDecls
                 pbottom <- instantiateEq base
                 return $ [Particle "base" [Conjecture "fixbase" pbottom]]

             stepAxioms = do
                 addFunsFromDecls stepDecls
                 addUnrecFunsFromDecls fundecls fixedFuns
                 phyp  <- instantiateEq hyp
                 pstep <- instantiateEq step
                 return $ [Particle "step"
                                 [Axiom "fixhyp" phyp
                                 ,Conjecture "fixstep" pstep]]


approximate :: Name -> Type -> TM (Name,[T.Decl])
approximate f ty = do
    let tyname = case ty of TyCon n _ -> n
                            TyVar{}   -> error "approximate on tyvar"
                            TyApp{}   -> error "approximate on tyapp"
    let n = "approx."
    wdproof "Lookup constructors from approximate"
    cons <- lookupConstructors tyname
    matrix <- forM cons $ \c -> do
                 Just ct <- lookupType c
                 let recs = recursiveArgs ct
                     vars = [ 'a':show i | (i,_) <- zip [(0 :: Int)..] recs ]
                 return ([PCon c (map PVar vars)] -- f (C x1 .. xn)
                        ,Nothing                  -- no guard
                        ,Con c [ if rec then App f [Var arg] else Var arg
                               | (rec,arg) <- zip recs vars ])
    addFuns [(n,1)]
    let decl = funcMatrix n matrix
    wdproof $ prettyCore decl
    (_,theory) <- translate decl
    return (n,theory)


-- | Is a type finite in a theory?
finiteType :: Theory -> Type -> Bool
finiteType thy n = undefined

-- These were added since StructuralInduction sometimes returns empty
-- parts because it overflowed the number allowed hyps or steps, and
-- this was inside the monad so this was the easiest fix, but yes -
-- an Ugly Hack!
removeEmptyParts :: Property -> Property
removeEmptyParts (Property n c parts)
  = Property n c (filter (not . null . snd . partMatter) parts)

-- | Takes a theory, and prepares the invocations
--   for a property and adds the lemmas
theoryToInvocations :: Params -> Theory -> Prop -> [Prop] -> (Property,[Msg])
theoryToInvocations params theory prop@(Prop{..}) lemmas =
    let partsm = makeProofDecls params theory prop lemmas
        (parts,dbg) = unzip $ flip map partsm $ \partm -> runTM params $ do
                        wdproof $ propName
                        addCons (thyDatas theory)
                        let funs = map (declName &&& length . declArgs) (theoryFunDecls theory)
                        addFuns funs
                        part <- partm
                        lemmaTPTP <- mapM translateLemma lemmas
                        mapM_ (uncurry registerFunPtr) (theoryUsedPtrs theory)
                        extra <- envStDecls
                        db    <- popMsgs
                        return (extendPart (extra ++ theoryFunTPTP theory ++ lemmaTPTP) part,db)
        property = Property { propName   = propName
                            , propCode   = propRepr
                            , propMatter = parts
                            }
    in (removeEmptyParts property,concat dbg)

{-
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