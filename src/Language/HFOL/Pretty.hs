{-# LANGUAGE TypeSynonymInstances #-}
module Language.HFOL.Pretty (prettyCore) where

import Language.HFOL.Core
import Text.PrettyPrint.HughesPJ

prettyCore :: P a => a -> String
prettyCore = render . p

class P a where
  p :: a -> Doc

instance P Decl where
  p (Func n as b) = text n <+> hsep (map text as) <+> equals <+> p b <+> semi
  p (Data cs    ) = text "data" <+> hsep [text c <+> int a | (c,a) <- cs] <+> semi

instance P Body where
  p (Case e brs) = text "case" <+> p e <+> text "of" <+> lbrace
                   $$ nest 4 (vcat (punctuate semi (map p brs)))
                   $$ rbrace
  p (Expr e)     = p e

instance P Expr where
  p = pexpr 2

enclose True  = parens
enclose False = id

pexpr :: Int -> Expr -> Doc
--pexpr l (App n []) = error "app empty"     -- This is an invariant that should be true
pexpr l (App n es) = enclose (l <= 1) $ text n <+> hsep (map (pexpr 1) es)
pexpr l (Con n es) = enclose (l <= 1) $ text n <+> hsep (map (pexpr 1) es)
pexpr _ (Var n)    = text n

instance P Branch where
  p (pat :-> e) = p pat <+> text "->" <+> p e

instance P Pattern where
  p = ppat 2

ppat :: Int -> Pattern -> Doc
ppat _ PWild       = text "_"
ppat _ (PVar n)    = text n
ppat _ (PCon n []) = text n
ppat l (PCon n ps) = enclose (l <= 1) (text n <+> hsep (map (ppat 1) ps))

instance P Name where
  p = text

-- Orphan instances
instance Show Decl where show = prettyCore
instance Show Body where show = prettyCore
instance Show Expr where show = prettyCore
instance Show Branch where show = prettyCore
instance Show Pattern where show = prettyCore
