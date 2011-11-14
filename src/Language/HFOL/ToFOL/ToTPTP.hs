{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns, ParallelListComp #-}
module Language.HFOL.ToFOL.ToTPTP where

import Language.HFOL.ToFOL.Core
import Language.HFOL.ToFOL.FixBranches
import Language.HFOL.ToFOL.Pretty
import Language.HFOL.ToFOL.Monad
import Language.HFOL.ToFOL.Constructors
import Language.HFOL.ToFOL.ProofDatatypes
import Language.HFOL.ToFOL.MakeProofs
import Language.HFOL.ToFOL.TranslateExpr
import Language.HFOL.Util
import Language.HFOL.FromHaskell.Names
import Language.TPTP hiding (Decl,Var)
import Language.TPTP.Pretty
import qualified Language.TPTP as T

import Control.Arrow ((&&&))
import Control.Applicative
import Control.Monad

import Data.List (intercalate,sort,find)
import Data.Maybe (catMaybes)

-- | Translates a program to TPTP, with its debug output
--   First argument is if proof mode is on or not
toTPTP :: Bool -> [Decl] -> ([(Decl,[T.Decl])],[T.Decl],[ProofDecl],Debug)
toTPTP p ds = runTM p $ do
                addFuns funs
                addCons datadecls'
                addTypes types
                faxioms <- mapM translate (filter funcDecl ds)
                extra   <- envStDecls
                db      <- popDebug
                proofs  <- getProofDecls
                return (faxioms,extra,proofs,db)
  where
    (fundecls,datadecls,typedecls) = partitionDecls ds
    funs = map (declName &&& length . declArgs) fundecls
    types = map (declName &&& declType) typedecls
    datadecls' = [Data "empty"  [] [Cons bottomName []]
                 ,Data "Bool"   [] [Cons trueName [],Cons falseName []]
                 ,Data unitName [] [Cons unitName []]
                 ,Data listTypeName ["a"] [Cons nilName [],Cons consName [TyVar "a",TyCon listTypeName [TyVar "a"]]]
                 ] ++
                 [Data (tupleName n) (take n tyvars) [Cons (tupleName n) (map TyVar (take n tyvars))]
                 | n <- [2..5] ]
                 ++ filter (\d -> not p || declName d `notElem` proofDatatypes) datadecls
    tyvars = map return ['a'..]

-- | Translate a function declaration to axioms,
--   together with its original definition for latex output.
--   If this is a proof object, handle it accordingly.
--   Most of that work is in Language.HFOL.ToFOL.ProofDecls
translate :: Decl -> TM (Decl,[T.Decl])
translate d@(Func fname args (Expr e)) = locally $ do
    pm <- getProofMode
    case () of
      () | pm && fname `elem` proveFunctions
            -> do write $ "skipped proof definition " ++ fname
                  return (d,[])
         | pm && provable e
            -> do makeProofDecls fname args e
                  return (d,[])
         | otherwise -> do
            rhs <- translateExpr (App fname (map Var args))
            lhs <- translateExpr e
            f <- Axiom fname <$> forallUnbound (rhs === lhs)
            write (prettyTPTP f)
            return (d,[f])

translate d@(Func fname args (Case scrutinee brs)) = (,) d . catMaybes <$> do
    write $ "translate " ++ prettyCore d
    write   "branches fixed to:"
    write $ prettyCore (Func fname args (Case scrutinee
                                         (fixBranches scrutinee brs)))
    sequence
      [ do mf <- indented
               $ locally
               $ translateBranch (modifyPattern nameWilds p)
                                 e
                                 (map brPMG prevbrs)
                                 num
           case mf of
             Just f  -> write (prettyTPTP f)
             Nothing -> write "No formula produced."
           writeDelimiter
           return mf
      | (p :-> e,prevbrs) <- withPrevious (fixBranches scrutinee brs)
      | num <- [0..]
      ]
  where
    translateBranch :: PMG -> Expr -> [PMG] -> Int -> TM (Maybe T.Decl)
    translateBranch pmg expr prev num = do
      write $ "translateBranch " ++ fname ++ " " ++ unwords args ++ " ="
      indented $ do write $ "case " ++ prettyCore scrutinee ++ " of"
                    write $ prettyCore (pmg :-> expr)
      writeDelimiter
      mconds <- indented $ do conds <- scrutinee ~~ pattern pmg
                              return (addGuardConds conds (guardCondition pmg))
      writeDelimiter
      case mconds of
        Nothing -> return Nothing
        Just conds -> do
          lhs <- translateExpr (App fname (map Var args))
          rhs <- translateExpr expr
          write $ "conditions : " ++ show conds
          formula <- (lhs === rhs) `withConditions` conds
          patExpr <- followExpr (patternToExpr (pattern pmg))
          let constr = stripContradictions conds
                     $ moreSpecificPatterns patExpr prev

          write $ "moreSpecificPatterns of " ++ prettyCore pmg ++
                  " followed to " ++ prettyCore patExpr ++ " are:"
          indented $
            mapM_ write [ intercalate "," [ prettyCore n ++ " = " ++
                                            prettyCore p
                                          | (n,p) <- cons ]
                        | cons <- constr ]
          write "previous patterns are:"
          indented $ mapM_ write [ prettyCore p | p <- prev ]

          case find (\cr -> sort conds == sort cr) constr of
            Just x  -> do write $ "constraint " ++ show x ++
                                  " is equal to conditions!"
                          return Nothing
            Nothing -> do
              formula' <- formula `withConstraints` constr
              Just . T.Axiom (fname ++ show num) <$> forallUnbound formula'
translate d = error $ "translate on " ++ prettyCore d

-- | Translate a pattern to an expression. This is needed to get the
--   more specific pattern for a branch. This function in partial:
--   the PWild pattern does not exists, as the are named by nameWilds.
patternToExpr :: Pattern -> Expr
patternToExpr (PVar x)    = Var x
patternToExpr (PCon p ps) = Con p (map patternToExpr ps)
patternToExpr PWild       = error "patternToExpr on PWild: use nameWilds"

-- | Follow indirections of an expression
followExpr :: Expr -> TM Expr
followExpr (Var x) = do
  b <- lookupName x
  case b of
    Indirection e -> followExpr e
    _             -> return (Var x)
followExpr (Con c as) = Con c <$> mapM followExpr as
followExpr e          = return e

-- | The type of conditions. They stem from a case scrutinee being a function
--   application and matched against a constructor.
type Condition = (Expr,Pattern)


-- | "Unify" the scrutinee expression with the pattern, returning just
--   the conditions for this branch, or nothing if this branch is
--   unreachable. The wilds in the pattern must be named.
(~~),(~~~) :: Expr -> Pattern -> TM (Maybe [Condition])
e ~~ p = do write $ "[" ++ prettyCore e ++ " ~ " ++ prettyCore p ++ "]"
            e ~~~ p

Con c as ~~~ PCon c' ps | c == c'   = concatMaybe <$> zipWithM (~~) as ps
                        | otherwise = unreachable
e        ~~~ PVar n     = addIndirection n e                 >> noConditions
Var n    ~~~ p          = addIndirection n (patternToExpr p) >> noConditions
App f as ~~~ PCon c ps  = condition (App f as,PCon c ps)
_        ~~~ PWild      = error "~~~ on PWild: use nameWilds"
IsBottom{} ~~~ _        = error "~~~ on IsBottom"

-- | No conditions from this unification
noConditions :: TM (Maybe [Condition])
noConditions = return (return [])

-- | This branch is unreachable
unreachable :: TM (Maybe [Condition])
unreachable = write "unreachable" >> return Nothing

-- | Return a condition
condition :: Condition -> TM (Maybe [Condition])
condition (e,p) = do
  write $ "condition: " ++ prettyCore e ++ " = " ++ prettyCore p
  return . return . return $ (e,p)

-- | Let the conjuncted conditions imply the formula
withConditions :: Formula -> [Condition] -> TM Formula
withConditions phi []    = return phi
withConditions phi conds = do
  conds' <- mapM translateCond conds
  return $ foldr1 (/\) conds' ==> phi
    where
      translateCond :: Condition -> TM Formula
      translateCond (expr,pat) =
          liftM2 (===) (translateExpr expr)
                       (translateExpr (patternToExpr pat))

-- | The type of constraints. They come from the more specific patterns,
--   looking "upwards" in the patterns of the case.
type Constraint = (Expr,Pattern)

-- | Remove all constraint groups which have contradictions with the conditions
stripContradictions :: [Condition] -> [[Constraint]] -> [[Constraint]]
stripContradictions conds css = [ constr
                                | constr <- css, and [ not (contradict c c')
                                                     | c <- conds, c' <- constr
                                                     ]
                                ]

-- | The condition and the constraint contradicts each other, then we
--   can remove the whole constraint group this constraint comes from.
--
--   This happens for instance when we have p x == bottom as a condition
--   and p x == True as a constraint
contradict :: Condition -> Constraint -> Bool
contradict (e,p) (e',p') = e == e' && p /= p'

-- | The formula is true or one of the constraints are true
withConstraints :: Formula -> [[Constraint]] -> TM Formula
withConstraints f css =    -- write $ "withConstraints: "
                           -- indented $ mapM_ (write . show) css
                           foldl (\/) f . catMaybes
                             <$> mapM translateGroup css
  where
    -- And the constraints of a group
    translateGroup :: [Constraint] -> TM (Maybe Formula)
    translateGroup cs = do
        write $ "translateGroup " ++ show cs
        locally . indented $ do
          fs <- catMaybes <$> mapM translateConstraint cs
          if null fs then return Nothing
                     else return (Just (foldl1 (/\) fs))

    -- Translate a constraint
    translateConstraint :: Constraint -> TM (Maybe Formula)
    translateConstraint (e,p) = do
        t <- translateExpr e
        r <- invertPattern p e t
        if t == r then returnAndWrite Nothing  -- Equal by reflexivity
                  else returnAndWrite (Just (t === r))
      where returnAndWrite r = write (show (fmap prettyTPTP r)) >> return r
-- | Inverts a pattern into projections
--
-- > invertPattern (C (E a b) c) x =
-- >     C (E (E.0 (C.0 x)) (E.1 (C.0 x))) (C.1 x)
--
-- Also adds
--     a = C.0 (E.0 x)
--     b = C.0 (E.1 x)
--     c = C.1 x
invertPattern :: Pattern -> Expr -> Term -> TM Term
invertPattern (PVar v)        e x = addIndirection v e >> return x
invertPattern PWild           _ x = return x
invertPattern p@(PCon n pats) e x = do
  write $ "inverting pattern " ++ prettyCore p
  projs <- lookupProj n
  b <- lookupName n
  case b of
    ConVar c -> T.Fun c <$> sequence [ invertPattern pat
                                                     (App (funName proj) [e])
                                                     (T.Fun proj [x])
                                     | pat <- pats | proj <- projs ]
    _ -> error $ "invertPattern: unbound constructor " ++ n