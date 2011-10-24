module Language.HFOL.Bottom where

import Language.HFOL.Core

-- The name for bottom

bottomName :: Name
bottomName = "bottom"

bottomP :: Pattern
bottomP = pcon0 bottomName

bottom :: Expr
bottom = con0 bottomName

