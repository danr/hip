{-# LANGUAGE TypeSynonymInstances #-}
module Test.AutoSpec.Pretty where

import Test.AutoSpec.Core
import Text.PrettyPrint.HughesPJ

prettyCore :: P a => a -> String
prettyCore = render . p

class P a where
  p :: a -> Doc

instance P k => P (Decl k) where
  p (Fun n args e) = text n <+> hsep (map p args) <+> equals <+> p e <+> semi

instance P k => P (Expr k) where
  p = pexpr 3

enclose True  = parens
enclose False = id
  
pexpr l (Case n brs) = enclose (l <= 2) $ 
                            text "case" <+> text n <+> text "of" <+> lbrace
                         $$ nest 4 (vcat (map ((<> semi) . p) brs))
                         $$ rbrace 
pexpr l (App e1 e2) = enclose (l <= 1) $ pexpr 2 e1 <+> pexpr 1 e2
pexpr l (Cons n []) = text n
pexpr l (Cons n es) = enclose (l <= 1) $ text n <+> hsep (map (pexpr 1) es)
pexpr l (Var n)     = text n
pexpr l Fail        = text "fail"
pexpr l (e1 :| e2)  = pexpr 2 e1 <+> text "|" <+> pexpr 2 e2

instance P k => P (Branch k) where
  p (Branch pat e) = p pat <+> text "->" <+> p e

instance P k => P (Pattern k) where
  p (PVar n)     = text n
  p (PCons n []) = text n
  p (PCons n es) = parens (text n <+> hsep (map p es))

instance P Name where
  p = text
  
instance P NestedPat where
  p (NP x) = p x