module Language.HFOL.ToFOL.MakeProofs where

import Language.HFOL.ToFOL.TranslateExpr
import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.Monad
import Language.HFOL.ToFOL.Pretty

import Language.HFOL.ToFOL.ProofDatatypes

import Language.TPTP hiding (Decl,Var)
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad

powerset :: [a] -> [[a]]
powerset = filterM (const [False,True]) . reverse

-- So far, all arguments are assumed to be Nat with Z, S constructors :)
makeProofDecls :: Name -> [Name] -> Expr -> TM ()
makeProofDecls fname args e = case e of
    App "proveBool" [lhs] -> prove lhs (Con "True" [])
    App "prove" [Con ":=:" [lhs,rhs]] -> prove lhs rhs
    _ -> write $ "Error: makeProofDecl onp nonsense expression " ++ prettyCore e
  where
    prove :: Expr -> Expr -> TM ()
    prove lhs rhs = (addProofDecl . ProofDecl fname =<<) . forM (powerset args) $
       \indargs -> if null indargs
                      then Plain <$> zeroClause []
                      else do z <- zeroClause indargs
                              s <- succClause indargs
                              let n = length indargs
                              return $ Induction indargs [IndPart (replicate n "Z") z
                                                         ,IndPart (replicate n "S") s
                                                         ]
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
