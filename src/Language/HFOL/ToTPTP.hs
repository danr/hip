{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns #-}
module Language.HFOL.ToTPTP where

import Language.HFOL.Core
import Language.HFOL.RemoveOverlap
import Language.HFOL.Pretty
import Language.HFOL.ToTPTPMonad
import qualified Language.TPTP as T

import Control.Arrow ((&&&))
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

preludeEnv :: Env
preludeEnv = flip (foldr addCons) datatypes
           $ emptyEnv
  where
    datatypes :: [[(Name,Int)]]
    datatypes = [ [("Tup" ++ show x,x)] | x <- [0..4] ] ++
                [ [("Cons",2),("Nil",0)]
                , [("True",0),("False",0)]
                , [("Nothing",0),("Just",1)]
                ]

toTPTP :: [Decl] -> [T.Decl]
toTPTP ds = envStDecls env st ++ axioms
  where
    funs = map (funcName &&& length . funcArgs) ds
    env = addFuns funs preludeEnv
    (axioms,st) = runTPTP env (concat <$> mapM translate ds)

-- Notice that this function works well on an empty argument list
applyFun :: Name -> [T.Term] -> ToTPTP T.Term
applyFun n as = do
  b <- lookupVar n
  case b of
    QuantVar x          -> return (appFold (T.Var x) as)
    b@(boundName -> fn) -> do
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

forall :: [T.VarName] -> T.Formula -> T.Formula
forall [] phi = phi
forall xs phi = T.Forall xs phi

translate :: Decl -> ToTPTP [T.Decl]
translate (Func fn args (Expr e)) =
  let vars = makeVarNames (length args) in bindVars args vars $ do
    rhs <- applyFun fn (map T.Var vars)
    lhs <- translateExpr e
    return [T.Axiom (fn ++ "axiom") $ forall vars $ T.EqOp rhs (T.:==) lhs]
  -- TODO: Case case

translateExpr :: Expr -> ToTPTP T.Term
translateExpr (Var n) = applyFun n []
translateExpr e       = applyFun (exprName e) =<< mapM translateExpr (exprArgs e)
