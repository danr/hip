module Language.HFOL.ToFOL.MakeProofs where

import Language.HFOL.ToFOL.TranslateExpr
import Language.HFOL.ToFOL.TranslateDecl
import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.Monad
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.Util (putEither,concatMapM)

import Language.HFOL.ToFOL.ProofDatatypes

import Language.TPTP hiding (Decl,Var,VarName)
import Language.TPTP.Pretty
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

import Data.Either (partitionEithers)

powerset :: [a] -> [[a]]
powerset = map reverse . filterM (const [False,True]) . reverse

unprop :: Type -> Type
unprop (TyCon _ [t]) = t
unprop t             = t

makeProofDecl :: Decl -> TM (Maybe ProofDecl)
makeProofDecl (Func fname args (Expr e))
  | fname `elem` proveFunctions = do
      write $ "skipped proof definition " ++ fname
      return Nothing
  | otherwise = do
      mty <- lookupType fname
      case mty of
        Nothing -> do write $ "Error: Cannot prove without type signature"
                      return Nothing
        Just t  -> do
          let typedArgs = case t of TyApp ts -> zip args ts
                                    _        -> []
              resTy     = unprop $ case t of TyApp ts -> last ts
                                             t'       -> t'
          case e of
            App "proveBool" [lhs] -> Just <$> prove fname typedArgs resTy
                                                   lhs (Con "True" [])
            App "prove" [as] -> do let [lhs,rhs] = exprArgs as
                                   Just <$> prove fname typedArgs resTy lhs rhs
            _  -> do write $ "Error: makeProofDecl on " ++ prettyCore e
                     return Nothing
makeProofDecl d = do write $ "Error: makeProofDecl on " ++ prettyCore d
                     return Nothing

type Rec = Bool

type VarName = Name
type ConName = Name
type TyName  = Name
type SkolemName = Name
type LR a = Either a a

approximate :: Type -> TM (Name,[T.Decl])
approximate ty = do
    let tyname = case ty of TyCon n _ -> n
                            TyVar{}   -> error "approximate on tyvar"
                            TyApp{}   -> error "approximate on tyapp"
        n = "approx." ++ tyname
        f = "approx.f"
        pf = PVar f
    cons <- lookupConstructors tyname
    matrix <- forM cons $ \c -> do
                 Just ct <- lookupType c
                 let recs = recursiveArgs ct
                     args = [ 'a':show i | (i,_) <- zip [(0 :: Int)..] recs ]
                 return ([pf,PCon c (map PVar args)] -- f (C x1 .. xn)
                        ,Nothing                     -- no guard
                        ,Con c [ if rec then App f [Var arg] else Var arg
                               | (rec,arg) <- zip recs args ])
    addFuns [(n,2)]
    let decl = funcMatrix n matrix
    write $ prettyCore decl
    (_,axioms) <- translate decl
    return (n,axioms)

prove :: Name -> [(Name,Type)] -> Type -> Expr -> Expr -> TM ProofDecl
prove fname typedArgs resTy lhs rhs = locally $ do
    let indargs = filter (concreteType . snd) typedArgs
    simpleindbottom <- forM indargs (proofBySimpleInduction True)
--   neginds         <- forM indargs proofByNegInduction
    simpleind       <- forM indargs (proofBySimpleInduction False)
    approx          <- proofByApproxLemma
    return $ ProofDecl fname (approx : simpleindbottom ++ simpleind)
  where
    decorateArg :: Bool -> (VarName,Type) -> TM (VarName,[LR (ConName,[Rec])])
    decorateArg addBottom (n,TyCon t _) = do
       -- t is for instance Nat or List a
       -- cs is for instance (Zero :: Nat,Succ :: Nat -> Nat) or
       --                    (Nil :: [a],Cons :: a -> [a] -> [a])
       cs <- (if addBottom then ("Bottom":) else id) <$> lookupConstructors t

       lr <- forM cs $ \c -> do Just ct <- lookupType c
                                let h = recursiveArgs ct
                                return (putEither (or h) (c,h))

       write $ "decorateArg, " ++ n ++ " : " ++ show lr
       return (n,lr)
    decorateArg _ (n,t) = error $ "decorateArg " ++ n
                              ++ " on non-concrete type " ++ show t

    proofByApproxLemma :: TM ProofType
    proofByApproxLemma = locally $ do
         (approx,approxAxioms) <- approximate resTy
         let f = "approx.f"
         addFuns [(f,1)]
--         fs <- skolemFun 1 f
--         addIndirection f (Var fs)
         hyp <- locally $ do
                   lhs' <- translateExpr (App f [lhs])
                   rhs' <- translateExpr (App f [rhs])
                   forallUnbound (lhs' === rhs')
         step <- locally $ do
                   lhs' <- translateExpr (App approx [Var f,lhs])
                   rhs' <- translateExpr (App approx [Var f,rhs])
                   forallUnbound (lhs' === rhs')
         write $ "Approx lemma hyp:  " ++ prettyTPTP hyp
         write $ "Approx lemma step: " ++ prettyTPTP step
         return $ ApproxLemma (Axiom (fname ++ "approxhyp") hyp
                              :Conjecture (fname ++ "approxstep") step
                              :approxAxioms)

    proofBySimpleInduction :: Bool -> (VarName,Type) -> TM ProofType
    proofBySimpleInduction addBottom (v,t) = do
        (_,cons) <- decorateArg addBottom (v,t)
        parts <- mapM (uncurry (inductionPart v) . either id id) cons
        return $ Induction addBottom [v] parts

    inductionPart :: Name -> ConName -> [Rec] -> TM IndPart
    inductionPart v c recArgs = do
        skolems <- mapM (const (skolemize v)) recArgs
        ih <- sequence [ Axiom (fname ++ "indhyp" ++ v ++ s)
                             <$> instantiatePs [[(v,Var s)]]
                       | (s,b) <- zip skolems recArgs, b ]
        is <- Conjecture (fname ++ "indstep" ++ v)
                     <$> instantiatePs [[(v,Con c (map Var skolems))]]
        return (IndPart [c] (is:ih))

    proofByNegInduction :: [(VarName,Type)] -> TM ProofType
    proofByNegInduction argSubset = locally $ do
        args <- mapM (decorateArg True) argSubset
        skolems <- mapM (skolemize . fst) args
        steps <- zipWithM negInductionStep args skolems
        absurd <- Neg <$> instantiatePs [zipWith (\(v,_) sv -> (v,Var sv)) args skolems]
        write $ "Proof by neg induction on " ++ show argSubset ++ " done."
        return $ NegInduction (map fst args)
                              [Axiom (fname ++ "negind") (foldr (/\) absurd steps)]
{-        absurd <- Axiom (fname ++ "negind") . Neg
               <$> instantiatePs [zipWith (\(v,_) sv -> (v,Var sv)) args skolems]
        return $ NegInduction (map fst args) (steps ++ [absurd])
-}

    negInductionStep :: (VarName,[LR (ConName,[Rec])]) -> SkolemName -> TM T.Formula
    negInductionStep (v,cs) sv = do
        let (precedent,ancedents) = partitionEithers cs
            fixPre c r = [(v,Con c (map (\n -> Var (v ++ c ++ show n)) [1..length r]))]
            fixAnc c r = do projs <- lookupProj c
                                   -- why does this if statement look like this?
                            return [ if b then [(v,App (funName proj) [Var sv])] else []
                                   | (proj,b) <- zip projs r, b
                                   ]
        ih <- instantiatePs (map (uncurry fixPre) precedent)
        is <- instantiatePs =<< concatMapM (uncurry fixAnc) ancedents
        return (ih ==> is)
--        return (Axiom (fname ++ "negindstep" ++ v) (ih ==> is))

    instantiatePs :: [[(VarName,Expr)]] -> TM T.Formula
    instantiatePs bindss = locally $ do
         clauses <- forM bindss $ \binds -> do
            mapM_ (uncurry addIndirection) binds
            lhs' <- translateExpr lhs
            rhs' <- translateExpr rhs
            return (lhs' === rhs')
         forallUnbound (foldr1 (/\) clauses)
