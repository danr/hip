{-# LANGUAGE RecordWildCards #-}
module Autospec.ToFOL.MakeProofs where

import Autospec.ToFOL.TranslateExpr
import Autospec.ToFOL.TranslateDecl
import Autospec.ToFOL.Core
import Autospec.ToFOL.Constructors
import Autospec.ToFOL.Monad
import Autospec.ToFOL.Pretty
import Autospec.ToFOL.ProofDatatypes
import Autospec.ToFOL.NecessaryDefinitions
import Autospec.ToFOL.FixpointInduction
import Autospec.ToFOL.StructuralInduction hiding (VarName,ConName)
import Autospec.Util (putEither,concatMapM)

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

makeProofDecls :: [Decl] -> Set Name -> Type -> Decl -> [TM ProofDecl]
makeProofDecls fundecls recfuns ty (Func fname args (Expr e)) = do
    let typedArgs = case ty of TyApp ts -> zip args ts
                               _        -> []
        resTy     = unProp $ case ty of TyApp ts -> last ts
                                        t        -> t
        prove' :: Bool -> Expr -> Expr -> [TM ProofDecl]
        prove' = prove fundecls recfuns resTy fname typedArgs
    case e of
      App "proveBool" [lhs]             -> prove' False lhs (Con "True" [])
      App "prove" [App "=:=" [lhs,rhs]] -> prove' False lhs rhs
      App "=:=" [lhs,rhs]               -> prove' False lhs rhs
      App "prove" [App "=/=" [lhs,rhs]] -> prove' True  lhs rhs
      App "=/=" [lhs,rhs]               -> prove' True  lhs rhs
      _  -> []
makeProofDecls _ _ _ _ = []

type Rec = Bool

type VarName = Name
type ConName = Name
type TyName  = Name
type SkolemName = Name
type LR a = Either a a

prove :: [Decl]
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
      -> Bool
      -- ^ Disprove instead of proving
      -> Expr
      -- ^ LHS
      -> Expr
      -- ^ RHS
      -> [TM ProofDecl]
      -- ^ Resulting instructions how to do proof declarations for this
prove fundecls recfuns resTy fname typedArgs disprove lhs rhs =
    let indargs = filter (concreteType . snd) typedArgs
        powset = powerset indargs
    in  plainProof ++
        proofByFixpointInduction ++
        proofByApproxLemma ++
--        map (proofByStructInd True 2) (filter ((<2) .  length) powset) ++
--        map (proofByStructInd False 2) (filter ((<3) .  length) powset) ++
        map proofBySimpleInduction indargs
  where
    pstr :: String
    pstr = prettyCore lhs ++
           (if disprove then " !" else " ") ++
           "= " ++ prettyCore rhs

    equals | disprove  = (!=)
           | otherwise = (===)

    accompanyParts :: ProofType -> TM [ProofPart] -> TM ProofDecl
    accompanyParts prooftype partsm = do
        let funs = map (declName &&& length . declArgs) fundecls
        addFuns funs
        faxioms <- concatMapM (fmap snd . translate) fundecls
        parts   <- partsm
        return $ proofDecl fname prooftype faxioms pstr parts

    accompanyPartsWithDecls :: ProofType
                            -> [([Decl],TM [ProofPart])]
                            -> TM ProofDecl
    accompanyPartsWithDecls prooftype tup = proofDecl fname prooftype [] pstr <$>
        (flip concatMapM tup (\(fundecls',partms) -> do
            let funs = map (declName &&& length . declArgs) fundecls'
            addFuns funs
            locally $ do
                parts   <- partms
                faxioms <- concatMapM (fmap snd . translate) fundecls'
                return $ map (extendProofPart faxioms) parts))

    decorateArg :: (VarName,Type) -> TM (VarName,[LR (ConName,[Rec])])
    decorateArg (n,TyCon t _) = do
       -- t is for instance Nat or List a
       -- cs is for instance (Zero :: Nat,Succ :: Nat -> Nat) or
       --                    (Nil :: [a],Cons :: a -> [a] -> [a])
       dbproof "Lookup constructors from decorateArg"
       cs <- (bottomName:) <$> lookupConstructors t

       lr <- forM cs $ \c -> do
                 mct <- lookupType c
                 case mct of
                     Just ct -> do
                        let h = recursiveArgs ct
                        return (putEither (or h) (c,h))
                     Nothing -> error $ "Cannot find type " ++ c

       dbproof $ "decorateArg, " ++ n ++ " : " ++ show lr
       return (n,lr)
    decorateArg (n,t) = error $ "decorateArg " ++ n
                              ++ " on non-concrete type " ++ show t

    proofByStructInd :: Bool -> Int -> [(Name,Type)] -> TM ProofDecl
    proofByStructInd addBottom d ns = accompanyParts
      (StructuralInduction (map fst ns) addBottom d) $ do
        env <- getEnv addBottom
        let parts = structuralInduction ns env d
        forM parts $ \(IndPart hyps conj vars) -> locally $ do
--            forM vars $ \v -> addIndirection v (Var v)
            addFuns (zip vars (repeat 0))
            phyps <- mapM instP hyps
            pconj <- instP conj
            return $ Part (concat vars)
                          ( Conjecture "conj" pconj :
                          [ Axiom "hyp" phyp | phyp <- phyps ] )
                          (if addBottom then Fail else FiniteSuccess)
      where
        instP :: [Expr] -> TM T.Formula
        instP es = locally $ do
            zipWithM addIndirection (map fst ns) es
            instantiateP []



    proofBySimpleInduction :: (VarName,Type) -> TM ProofDecl
    proofBySimpleInduction (v,t) = accompanyParts (SimpleInduction v) $ do
        (_,cons) <- decorateArg (v,t)
        mapM (uncurry (inductionPart v) . either id id) cons

    inductionPart :: Name -> ConName -> [Rec] -> TM ProofPart
    inductionPart v c recArgs = do
        skolems <- mapM (const (skolemize v)) recArgs
        ih <- sequence [ Axiom ("indhyp" ++ v ++ s)
                             <$> instantiatePs [[(v,Var s)]]
                       | (s,b) <- zip skolems recArgs, b ]
        is <- Conjecture ("indstep" ++ v)
                     <$> instantiatePs [[(v,Con c (map Var skolems))]]
        return (Part c (is:ih) (if c == bottomName then InfiniteFail else Fail))

    instantiatePs :: [[(VarName,Expr)]] -> TM T.Formula
    instantiatePs bindss = locally $ do
         clauses <- forM bindss $ \binds -> do
            mapM_ (uncurry addIndirection) binds
            lhs' <- translateExpr lhs
            rhs' <- translateExpr rhs
            return (lhs' `equals` rhs')
         forallUnbound (foldr1 (/\) clauses)

    approxSteps :: TM (Formula,Formula,[T.Decl])
    approxSteps = do
        let f = "a.f"
        addFuns [(f,1)]
        (approx,approxAxioms) <- approximate f resTy
        hyp <- locally $ do
                  lhs' <- translateExpr (App f [lhs])
                  rhs' <- translateExpr (App f [rhs])
                  forallUnbound (lhs' `equals` rhs')
        step <- locally $ do
                  lhs' <- translateExpr (App approx [lhs])
                  rhs' <- translateExpr (App approx [rhs])
                  forallUnbound (lhs' `equals` rhs')
--        dbproof $ "Approx lemma hyp:  " ++ prettyTPTP hyp
--        dbproof $ "Approx lemma step: " ++ prettyTPTP step
        return (hyp,step,approxAxioms)

    -- Returns in the List monad instead of the Maybe monad
    proofByApproxLemma :: [TM ProofDecl]
    proofByApproxLemma
       | concreteType resTy =
             [accompanyParts ApproxLemma $ do
                   (hyp,step,approxAxioms) <- approxSteps
                   return $ [proofPart "step"
                                 (Axiom ("approxhyp") hyp
                                 :Conjecture ("approxstep") step
                                 :approxAxioms)]
             ]
       | otherwise = []

    plainProof :: [TM ProofDecl]
    plainProof
        | any (concreteType . snd) typedArgs = []
        | otherwise =
            return $ accompanyParts Plain $ do
            p <- instantiateP []
            return $ [Part "plain" [Conjecture "plain" p] EpicFail]

    instantiateP :: [(VarName,VarName)] -> TM T.Formula
    instantiateP binds = locally $ do
        lhs' <- translateExpr (substVars binds lhs)
        rhs' <- translateExpr (substVars binds rhs)
        forallUnbound (lhs' `equals` rhs')

    proofByFixpointInduction :: [TM ProofDecl]
    proofByFixpointInduction = concatMap
                                   instantiateFixProof
                                   (proofByFixpoint fundecls recfuns lhs rhs)
      where
        instantiateEq :: (Expr,Expr) -> TM T.Formula
        instantiateEq (l,r) = locally $ do
            l' <- translateExpr l
            r' <- translateExpr r
            forallUnbound (l' `equals` r')

        addFunsFromDecls ds = sequence_
           [ addFuns [(f,length as)] | Func f as _ <- ds ]

        addUnrecFunsFromDecls ds fixedFuns = sequence_
           [ addFuns [(f ++ unRec,length as)]
           | Func f as _ <- ds
           , f `elem` fixedFuns ]

        instantiateFixProof :: FixProof -> [TM ProofDecl]
        instantiateFixProof fp@(FixProof {..}) =
            [ accompanyPartsWithDecls (FixpointInduction fixedFuns)
                 [(baseDecls ++ fundecls,baseAxioms)
                 ,(stepDecls ++ fundecls,stepAxioms)]
{-            , accompanyPartsWithDecls (FiniteFixpointInduction fixedFuns)
                 [(fundecls,anyAxioms)
                 ,(stepDecls ++ fundecls,stepAxioms)] -}
            ]
          where
             baseAxioms = do
                 dbproof $ show fp
                 addFunsFromDecls baseDecls
                 pbottom <- instantiateEq base
                 return $ [proofPart "base" [Conjecture "fixbase" pbottom]]

             anyAxioms = do
                 dbproof $ show fp
                 panyt <- instantiateEq anyt
                 return $ [Part "anybase"
                                 [Conjecture "fixanybase" panyt]
                                 FiniteSuccess]

             stepAxioms = do
                 addFunsFromDecls stepDecls
                 addUnrecFunsFromDecls fundecls fixedFuns
                 phyp  <- instantiateEq hyp
                 pstep <- instantiateEq step
                 return $ [proofPart "step"
                                 [Axiom "fixhyp" phyp
                                 ,Conjecture "fixstep" pstep]]


approximate :: Name -> Type -> TM (Name,[T.Decl])
approximate f ty = do
    let tyname = case ty of TyCon n _ -> n
                            TyVar{}   -> error "approximate on tyvar"
                            TyApp{}   -> error "approximate on tyapp"
    let n = "approx."
    dbproof "Lookup constructors from approximate"
    cons <- lookupConstructors tyname
    matrix <- forM cons $ \c -> do
                 Just ct <- lookupType c
                 let recs = recursiveArgs ct
                     args = [ 'a':show i | (i,_) <- zip [(0 :: Int)..] recs ]
                 return ([PCon c (map PVar args)] -- f (C x1 .. xn)
                        ,Nothing                  -- no guard
                        ,Con c [ if rec then App f [Var arg] else Var arg
                               | (rec,arg) <- zip recs args ])
    addFuns [(n,1)]
    let decl = funcMatrix n matrix
    dbproof $ prettyCore decl
    (_,axioms) <- translate decl
    return (n,axioms)

