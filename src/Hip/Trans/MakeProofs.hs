{-# LANGUAGE RecordWildCards,TupleSections #-}
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

import Language.TPTP hiding (Decl,Var,VarName,declName)
import Language.TPTP.Pretty
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

import Data.Maybe (fromMaybe,mapMaybe)
import Control.Arrow ((&&&))

import Data.Set (Set)
import qualified Data.Set as S

powerset :: [a] -> [[a]]
powerset = init . filterM (const [True,False])

makeProofDecls :: TyEnv -> Params -> Theory -> Prop -> [Prop] -> [TM Part]
makeProofDecls env params theory prop@(Prop{..}) lemmas =
    let typedVars = case propType of TyApp ts -> zip propVars ts
                                     _        -> []

        resTy     = unProp (resType propType)

        fundecls  = theoryFunDecls theory

        recfuns   = theoryRecFuns theory

    in  prove env params fundecls recfuns resTy propName typedVars proplhs proprhs

prove :: TyEnv
      -- ^ The type environment
      -> Params
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
prove env params@(Params{..}) fundecls recfuns resTy fname typedVars lhs rhs =
    let indargs :: [(Name,Type)]
        indargs = filter (\(_,t) -> {- not (finiteTy env t) && -} concreteType t) typedVars
        powset :: [[(Name,Type)]]
        powset = powerset indargs
   in  concat $ [ plainProof                                  | 'p' `elem` methods ]

   -- When adding back fpi and approx, remember to type guard finite types!
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
                                                       [ Hypothesis "hyp" phyp | phyp <- phyps ]
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
                                      , particleMatter = Hypothesis "approxhyp" hyp
                                                       : Conjecture "approxstep" step
                                                       : approxAxioms
                                      }]
             ]
       | otherwise = []

    plainProof :: [TM Part]
    plainProof = return $ accompanyParts Plain Infinite $ do
                     p <- instantiateP []
                     return $ [ Particle "plain" [Conjecture "plain" p] ]


    instantiateP :: [(VarName,VarName)] -> TM T.Formula
    instantiateP binds = locally $ do
        lhs' <- translateExpr (substVars binds lhs)
        rhs' <- translateExpr (substVars binds rhs)
        tytms <- mapM (\(n,t) -> (,t) <$> translateExpr (Var n)) typedVars
        forallUnbound (typeGuards env tytms (lhs' === rhs'))

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
           [ addFuns [(f,length as)] |Func f  as _ <- ds ]

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
                                 [Hypothesis "fixhyp" phyp
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
    let tyEnv  = theoryTyEnv theory
        partsm = makeProofDecls tyEnv params theory prop lemmas
        (parts,dbg) = unzip $ flip map partsm $ \partm -> runTM params $ do
                        wdproof $ propName
                        addCons (thyDatas theory)
                        let funs = map (declName &&& length . declArgs) (theoryFunDecls theory)
                        addFuns funs
                        part <- partm
                        lemmaTPTP <- mapM translateLemma lemmas
                        mapM_ (uncurry registerFunPtr) (theoryUsedPtrs theory)
                        extra    <- envStDecls
                        let tyaxioms = map (genTypePred tyEnv)         (theoryDataTypes theory)
                                    ++ mapMaybe (infDomainAxiom tyEnv) (theoryDataTypes theory)
                                    ++ [anyTypeAxiom]
                        db    <- popMsgs
                        return (extendPart (extra ++ tyaxioms ++ theoryFunTPTP theory ++ lemmaTPTP) part,db)
        property = Property { propName   = propName
                            , propCode   = propRepr
                            , propMatter = parts
                            }
    in (removeEmptyParts property,concat dbg)

