module Language.HFOL.ToFOL.MakeProofs where

import Language.HFOL.ToFOL.TranslateExpr
import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.Monad
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.Util (putEither,concatMapM)

import Language.HFOL.ToFOL.ProofDatatypes

import Language.TPTP hiding (Decl,Var,VarName)
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

import Data.Either (partitionEithers)

powerset :: [a] -> [[a]]
powerset = map reverse . filterM (const [False,True]) . reverse

-- So far, all arguments are assumed to be Nat with Z, S constructors :)
makeProofDecls :: Name -> [Name] -> Expr -> TM ()
makeProofDecls fname args e = do
    mty <- lookupType fname
    case mty of
        Nothing -> write $ "Error: Cannot prove without type signature"
        Just t  -> do
            let typedArgs = case t of TyApp ts -> zip args ts
                                      _        -> []
            case e of
                App "proveBool" [lhs] -> prove fname typedArgs lhs (Con "True" [])
                App "prove" [as] -> let [lhs,rhs] = exprArgs as
                                    in  prove fname typedArgs lhs rhs
                _ -> write $ "Error: makeProofDecl on nonsense expression " ++ prettyCore e

type Rec = Bool

type VarName = Name
type ConName = Name
type TyName  = Name
type SkolemName = Name
type LR a = Either a a

prove :: Name -> [(Name,Type)] -> Expr -> Expr -> TM ()
prove fname typedArgs lhs rhs = do
   r <- forM (powerset (filter (concrete . snd) typedArgs)) proofByNegInduction
   addProofDecl (ProofDecl fname r)

  where
    -- Can only do induction on concrete types obviously
    concrete TyCon{} = True
    concrete _       = False

    hyp :: Type -> [Bool]
    hyp (TyApp ts) = let t = last ts
                     in  map (== t) (init ts)
    hyp _          = []

    decorateArg :: (VarName,Type) -> TM (VarName,[LR (ConName,[Rec])])
    decorateArg (n,TyCon t _) = do
       -- t is for instance Nat or List a
       -- cs is for instance (Zero :: Nat,Succ :: Nat -> Nat) or
       --                    (Nil :: [a],Cons :: a -> [a] -> [a])
       cs <- lookupConstructors t
       lr <- forM cs $ \c -> do Just ct <- lookupType c
                                let h = hyp ct
                                return (putEither (or h) (c,h))
       write $ "decorateArg, " ++ n ++ " : " ++ show lr
       return (n,lr)

    proofByNegInduction :: [(Name,Type)] -> TM ProofType
    proofByNegInduction argSubset = locally $ do
        args <- mapM decorateArg argSubset
        skolems <- mapM (skolemize . fst) args
        steps <- zipWithM inductionStep args skolems
        absurd <- Neg <$> instantiatePs [zipWith (\(v,_) sv -> (v,Var sv)) args skolems]
        return $ NegInduction (map fst args)
                              [Axiom (fname ++ "negind") (foldr (/\) absurd steps)]
{-        absurd <- Axiom (fname ++ "negind") . Neg
               <$> instantiatePs [zipWith (\(v,_) sv -> (v,Var sv)) args skolems]
        return $ NegInduction (map fst args) (steps ++ [absurd])
-}

    inductionStep :: (VarName,[LR (ConName,[Rec])]) -> SkolemName -> TM T.Formula
    inductionStep (v,cs) sv = do
        let (precedent,ancedents) = partitionEithers cs
            fixPre c r = [(v,Con c (map (\n -> Var (v ++ c ++ show n)) [1..length r]))]
            fixAnc c r = do projs <- lookupProj c
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
