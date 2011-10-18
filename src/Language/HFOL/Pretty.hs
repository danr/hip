{-# LANGUAGE TypeSynonymInstances #-}
module Language.HFOL.Pretty where

import Language.HFOL.Core
import Text.PrettyPrint.HughesPJ

prettyCore :: P a => a -> String
prettyCore = render . p

class P a where
  p :: a -> Doc

instance P Decl where
  p (Func n as b) = text n <+> hsep (map text as) <+> equals <+> p b <+> semi

instance P Body where
  p (Case e brs) = text "case" <+> p e <+> text "of" <+> lbrace
                   $$ nest 4 (vcat (map ((<> semi) . p) brs))
                   $$ rbrace
  p (Expr e)     = p e

instance P Expr where
  p = pexpr 2

enclose True  = parens
enclose False = id
  
pexpr l (App e1 e2) = enclose (l <= 1) $ pexpr 2 e1 <+> pexpr 1 e2
pexpr l (Con n [])  = text n
pexpr l (Con n es)  = enclose (l <= 1) $ text n <+> hsep (map (pexpr 1) es)
pexpr l (Var n)     = text n

instance P Branch where
  p (pat :-> e) = p pat <+> text "->" <+> p e

instance P Pattern where
  p = ppat 2
  
ppat l Default     = char '_'
ppat l (PVar n)    = text n
ppat l (PCon n []) = text n
ppat l (PCon n ps) = enclose (l <= 1) (text n <+> hsep (map (ppat 1) ps))

instance P Name where
  p = text
