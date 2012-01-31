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

makeProofDecls :: [Decl] -> Set Name -> Type -> Decl -> [TM Part]
makeProofDecls fundecls recfuns ty (Func fname args (Expr e)) = do
    let typedArgs = case ty of TyApp ts -> zip args ts
                               _        -> []

        resTy     = unProp $ case ty of TyApp ts -> last ts
                                        t        -> t

        prove' :: Expr -> Expr -> [TM Part]
        prove' lhs rhs = case resTy of
              -- Prop (a -> b) ~= a -> Prop b
              TyApp ts -> let extraTyArgs =  zip [ "x." ++ show x | x <- [0..] ]
                                                 (init ts)
                          in  prove fundecls recfuns
                                    (last ts)
                                    fname
                                    (typedArgs ++ extraTyArgs)
                                    (foldl app lhs (map (Var . fst) extraTyArgs))
                                    (foldl app rhs (map (Var . fst) extraTyArgs))
              _        -> prove fundecls recfuns resTy fname typedArgs lhs rhs
    case e of
      App "proveBool" [lhs]             -> prove' lhs (Con "True" [])
      App "prove" [App "=:=" [lhs,rhs]] -> prove' lhs rhs
      App "=:=" [lhs,rhs]               -> prove' lhs rhs
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
      -> Expr
      -- ^ LHS
      -> Expr
      -- ^ RHS
      -> [TM Part]
      -- ^ Resulting instructions how to do proof declarations for this
prove fundecls recfuns resTy fname typedArgs lhs rhs =
    let indargs = filter (concreteType . snd) typedArgs
        powset = powerset indargs
    in  plainProof
     ++ proofByFixpointInduction
     ++ proofByApproxLemma
     ++ map (proofByStructInd True 2) (filter ((<2) .  length) powset)
     ++ map (proofByStructInd False 2) (filter ((<2) .  length) powset)
--        map proofBySimpleInduction indargs
  where
    accompanyParts :: ProofMethod -> Coverage -> TM [Particle] -> TM Part
    accompanyParts prooftype coverage partsm = do
        let funs = map (declName &&& length . declArgs) fundecls
        addFuns funs
        theory <- concatMapM (fmap snd . translate) fundecls
        parts   <- partsm
        return $ Part { partMethod     = prooftype
                      , partCoverage   = coverage
                      , partMatter     = (theory,parts)
                      }


    accompanyPartsWithDecls :: ProofMethod
                            -> Coverage
                            -> [([Decl],TM [Particle])]
                            -> TM Part
    accompanyPartsWithDecls prooftype coverage tup = do
         parts <- flip concatMapM tup $ \(fundecls',partms) -> do
            let funs = map (declName &&& length . declArgs) fundecls'
            addFuns funs
            locally $ do
                parts   <- partms
                theory <- concatMapM (fmap snd . translate) fundecls'
                return $ map (extendParticle theory) parts
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
        forM parts $ \(IndPart hyps conj vars) -> locally $ do
--            forM vars $ \v -> addIndirection v (Var v)
            addFuns (zip vars (repeat 0))
            phyps <- mapM instP hyps
            pconj <- instP conj
            return $ Particle { particleDesc   = unwords vars
                              , particleMatter = Conjecture "conj" pconj :
                                                 [ Axiom "hyp" phyp | phyp <- phyps ]
                              }
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
        | any (concreteType . snd) typedArgs = []
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
                                   (proofByFixpoint fundecls recfuns lhs rhs)
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
                 [(baseDecls ++ fundecls,baseAxioms)
                 ,(stepDecls ++ fundecls,stepAxioms)]
            ]
          where
             baseAxioms = do
                 dbproof $ show fp
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

{- Old code for simple induction
    proofBySimpleInduction :: (VarName,Type) -> TM Part
    proofBySimpleInduction (v,t) = accompanyParts (SimpleInduction v) $ do
        (_,cons) <- decorateArg (v,t)
        mapM (uncurry (inductionPart v) . either id id) cons

    inductionPart :: Name -> ConName -> [Rec] -> TM Particle
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
            return (lhs' === rhs')
         forallUnbound (foldr1 (/\) clauses)

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
                     Nothing -> error $ "Cannot find type " ++

       dbproof $ "decorateArg, " ++ n ++ " : " ++ show lr
       return (n,lr)
    decorateArg (n,t) = error $ "decorateArg " ++ n
                              ++ " on non-concrete type " ++ show t
-}


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
    (_,theory) <- translate decl
    return (n,theory)

