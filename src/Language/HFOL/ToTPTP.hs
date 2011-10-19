{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.HFOL.ToTPTP where

import Language.HFOL.Core
import Language.HFOL.RemoveOverlap
import Language.HFOL.Pretty
import Language.HFOL.ToTPTPMonad
import qualified Language.TPTP as T

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

preludeEnv :: Env
preludeEnv = flip (foldr (uncurry addProj')) (concat datatypes)
           $ flip (foldr (addCons)) (map (map fst) datatypes)
           $ emptyEnv
  where
    datatypes :: [[(Name,Int)]]
    datatypes = [ [("Tup" ++ show x,x)] | x <- [2..4] ] ++
                [ [("Cons",2),("Nil",0)]
                , [("True",0),("False",0)]
                , [("Nothing",0),("Just",1)]
                ]

--toTPTP :: [Decl] -> [T.Decl]
--toTPTP =

mkFun :: Name -> [Name] -> T.Term
mkFun n [] = T.Var (T.VarName n)
mkFun n as = T.Fun (T.FunName n) (map (T.Var . T.VarName) as)

translate :: Decl -> ToTPTP [T.Decl]
translate (Func fn args (Expr e)) = do
  lhs <- translateExpr e
  return [T.Axiom (fn ++ "axiom") $ T.EqOp (mkFun fn args) (T.:==) lhs]
  -- TODO: Case case

translateExpr :: Expr -> ToTPTP T.Term
translateExpr (Var n)    = return $ T.Var (T.VarName n)
translateExpr (Con n []) = return $ T.Var (T.VarName n)
translateExpr e          = T.Fun (T.FunName (exprName e))
                                 <$> mapM translateExpr (exprArgs e)