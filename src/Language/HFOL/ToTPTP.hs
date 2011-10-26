{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns, ParallelListComp #-}
module Language.HFOL.ToTPTP where

import Language.HFOL.Core
import Language.HFOL.FixBranches
import Language.HFOL.Pretty
import Language.HFOL.Monad
import Language.HFOL.Util
import Language.HFOL.Bottom
import Language.TPTP hiding (Decl,Var)
import Language.TPTP.Pretty
import qualified Language.TPTP as T

import Control.Arrow ((&&&))
import Control.Applicative
import Control.Monad

import Data.List (partition,intercalate)
import Data.Maybe (catMaybes,maybeToList)

-- | Translates a program to TPTP, with its debug output
toTPTP :: [Decl] -> ([(Decl,[T.Decl])],[T.Decl],Debug)
toTPTP ds = runTM $ do
               addFuns funs
               addCons datatypes
               faxioms <- mapM translate (filter funcDecl ds)
               extra   <- envStDecls
               db      <- popDebug
               return (faxioms,extra,db)
  where
    (funs,datatypes) =
      let (funs',datatypes') = partition funcDecl ds
      in  (map (funcName &&& length . funcArgs) funs'
          ,[(bottomName,0)] : map dataCons datatypes')

-- | Translate an expression to a term
translateExpr :: Expr -> TM Term
translateExpr (Var n) = applyFun n []
translateExpr e       = applyFun (exprName e) =<< mapM translateExpr (exprArgs e)

-- | Apply a function/constructor name to an argument list
--   Follows the function definition if it is an indirection
--   Notice that this function works well on an empty argument list
applyFun :: Name -> [Term] -> TM Term
applyFun n as = do
  b <- lookupName n
  case b of
    QuantVar x        -> return (appFold (T.Var x) as)
    Indirection e     -> do t <- translateExpr e
                            return (appFold t as)
    (boundName -> fn) -> do
      arity <- lookupArity n
      if length as < arity
        then -- Partial application
          do useFunPtr n
             return $ appFold (T.Fun (makeFunPtrName fn) []) as
        else -- Function has enough arguments, and could possibly have more
          do -- (for functions returning functions)
             when (boundCon b && length as > arity) $ error $ "Internal error: "
                 ++ "constructor " ++ n ++ "applied to too many arguments."
             return $ appFold (T.Fun fn (take arity as)) (drop arity as)

-- | Translate a function declaration to axioms,
--   together with its original definition for latex output.
translate :: Decl -> TM (Decl,[T.Decl])
translate d@(Func fname args (Expr e)) = locally $ do
    rhs <- translateExpr (App fname (map Var args))
    lhs <- translateExpr e
    qs  <- popQuantified
    let f = Axiom fname $ forall qs $ rhs === lhs
    write (prettyTPTP f)
    return (d,[f])
translate d@(Func fname args (Case scrutinee brs)) = (,) d . catMaybes <$> do
    write $ "translate " ++ prettyCore d
    write $ "branches fixed to:"
    write $ prettyCore (Func fname args
                                               (Case scrutinee
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
      writeDelimiter
      write $ "translateBranch " ++ fname ++ " " ++ unwords args ++ " ="
      indented $ do write $ "case " ++ prettyCore scrutinee ++ " of"
                    write $ prettyCore (pmg :-> expr)
      writeDelimiter
      mconds <- indented $ (`addConds` guardCondition pmg)
                        <$> scrutinee ~~ pattern pmg
      writeDelimiter
      case mconds of
        Nothing -> return Nothing
        Just conds -> do
          lhs <- translateExpr (App fname (map Var args))
          rhs <- translateExpr expr
          write $ "conditions : " ++ show conds
          formula <- (lhs === rhs) `withConditions` conds
          patExpr <- followExpr (patternToExpr (pattern pmg))
          let constr = stripConflicts conds
                     $ map flattenPMGConstraints
                     $ moreSpecificPatterns patExpr prev

          write $ "moreSpecificPatterns of " ++ prettyCore pmg ++
                  " followed to " ++ prettyCore patExpr ++ " are:"
          indented $
            mapM_ write [ intercalate "," [ prettyCore n ++ " = " ++ prettyCore p
                                          | (n,p) <- cons ]
                        | cons <- constr ]
          write "previous patterns are:"
          indented $ mapM_ write [ prettyCore p | p <- prev ]

          formula' <- formula `withConstraints` constr
          qs <- popQuantified
          return $ Just $ T.Axiom (fname ++ show num) (forall qs formula')
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

addConds :: Maybe [a] -> Maybe a -> Maybe [a]
addConds (Just xs) (Just y) = Just (y : xs)
addConds Nothing   _        = Nothing
addConds xs        Nothing  = xs

guardCondition :: PMG -> Maybe Condition
guardCondition (NoGuard _)            = Nothing
guardCondition (Guard _ (IsBottom e)) = Just (e,bottomP)
guardCondition (Guard _ e           ) = Just (e,pcon0 "True")

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

flattenPMGConstraints :: [(Expr,PMG)] -> [Constraint]
flattenPMGConstraints ((e,pmg):pmgs) = [(e,pattern pmg)]
                                    ++ maybeToList (guardCondition pmg)
                                    ++ flattenPMGConstraints pmgs
flattenPMGConstraints [] = []

-- | Remove all constraint groups which have conflicts with the conditions
stripConflicts :: [Condition] -> [[Constraint]] -> [[Constraint]]
stripConflicts conds css = [ constr
                           | constr <- css, and [ not (conflict c c')
                                                | c <- conds, c' <- constr
                                                ]
                           ]

-- | The condition and the constraint is in conflict, then we can remove
--   the whole constraint group this constraint comes from.
--
--   This happens for instance when we have p x == bottom as a condition
--   and p x == True as a constraint
conflict :: Condition -> Constraint -> Bool
conflict (e,p) (e',p') = e == e' && p /= p'


-- | The formula is true or one of the constraints are true
withConstraints :: Formula -> [[Constraint]] -> TM Formula
withConstraints f css = do -- write $ "withConstraints: "
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

returnAndWrite r = write (show (fmap prettyTPTP r)) >> return r
-- | Inverts a pattern into projections
--
-- > invertPattern (C (E a b) c) x =
-- >     C (E (E.0 (C.0 x)) (E.1 (C.0 x))) (C.1 x)
--
-- Also adds
--     a = C.0 (E.0 x)
--     b = C.0 (E.1 x)
--     c = C.1 x
invertPattern :: Pattern -> Expr -> Term -> TM (Term)
invertPattern (PVar v)        e x = addIndirection v e >> return x
invertPattern PWild           _ x = return x
invertPattern p@(PCon n pats) e x = do
  write $ "inverting pattern " ++ prettyCore p
  projs <- lookupProj n
  b <- lookupName n
  case b of
    ConVar c -> T.Fun c <$> sequence [ invertPattern pat (App (funName proj) [e])
                                                         (T.Fun proj [x])
                                     | pat <- pats | proj <- projs ]
    _ -> error $ "invertPattern: unbound constructor " ++ n