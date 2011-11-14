module Language.HFOL.ToFOL.MakeProofs where

import Language.HFOL.ToFOL.TranslateExpr
import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.Monad
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.ToFOL.Util (concatMapM)

import Language.HFOL.ToFOL.ProofDatatypes

import Language.TPTP hiding (Decl,Var)
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

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
                App "prove" [Con ":=:" [lhs,rhs]] -> prove fname typedArgs lhs rhs
                _ -> write $ "Error: makeProofDecl on nonsense expression " ++ prettyCore e

prove :: Name -> [(Name,Type)] -> Expr -> Expr -> TM ()
prove fname typedArgs lhs rhs = do
   r <- forM (powerset (filter (concrete . snd) typedArgs)) proofByInduction
   addProofDecl (ProofDecl fname r)

{-
   \indargs -> if null indargs
                  then Plain <$> zeroClause []
                  else do z <- zeroClause indargs
                          s <- succClause indargs
                          let n = length indargs
                          return $ Induction indargs [IndPart (replicate n "Z") z
                                                     ,IndPart (replicate n "S") s
-}

  where
    -- Can only do induction on concrete types obviously
    concrete TyCon{} = True
    concrete _       = False

    hyp :: Type -> [Bool]
    hyp (TyApp ts) = let t = last ts
                     in  map (== t) (init ts)
    hyp _          = []


    ind :: [(Name,Name,[Bool])]
        -- ^ var , constructor , induct
        -> WriterT [T.Decl] TM [(Name,Expr)]
        -- ^ var , new expr , ih decls
    ind [] = do
      lhs' <- translateExpr lhs
      rhs' <- translateExpr rhs
      qs   <- popQuantified
      tell [Conjecture "" (forall' qs $ lhs' === rhs')]
      return []
    ind ((var,con,cs):xs) = do
      cs' <- forM (zip [0..] cs) $ \(n,c) -> do
                   let n = var ++ "_" ++ n ++ "_"
                   if c then lift (skolem n) else return n

      guard c
      s <- skolem c
      r <- ind xs
      return ((a,Con con [ if n == c then | (n,c') <- cs]):r)

    fst4 (a,b,c,d) = a
    snd4 (a,b,c,d) = b
    trd4 (a,b,c,d) = c
    fth4 (a,b,c,d) = d

    proofByInduction tyArgs = do
        -- The different constructors for each argument
        conArgs <- mapM (\(n,TyCon c as) -> (,) n <$> lookupType c) tyArgs
        let steps :: [[(Name,Name)]]
            steps = sequence conArgs
        r <- forM steps $ \s -> locally $ do
            s' <- ind <$> concatMapM (\(n,c) -> lookupType c >>= \t -> map ((,,) n c) (hyp t)) s
            (ih,skolems) <- flip mapAndUnzipM s' $ \kluns ->
                               forM kluns $ \(var,cons,indvar,vlist) ->


       return $ Induction (map fst tyArgs) r

   where
     zeroClause indargs = locally $ do
       forM_ indargs (`addIndirection` (Con "Z" []))
       lhs' <- translateExpr lhs
       rhs' <- translateExpr rhs
       qs   <- popQuantified
       return [Conjecture (fname ++ "base" ++ concat indargs)
                          (forall' qs $ lhs' === rhs')]
     succClause indargs = locally $ do
         skolems <- forM indargs skolem
         ih <- do
           lhs' <- translateExpr lhs
           rhs' <- translateExpr rhs
           qs <- popQuantified
           return (Axiom (fname ++ "hyp" ++ concat indargs)
                         (forall' qs $ lhs' === rhs'))
         is <- do
           zipWithM_ (\n s -> addIndirection n (Con "S" [Var s])) indargs skolems
           lhs' <- translateExpr lhs
           rhs' <- translateExpr rhs
           qs <- popQuantified
           return (Conjecture (fname ++ "step" ++ concat indargs)
                              (forall' qs $ lhs' === rhs'))
         return [ih,is]
