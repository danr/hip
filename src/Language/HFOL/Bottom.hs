module Language.HFOL.Bottom where

import Language.HFOL.Core

-- | The name for bottom
bottomName :: Name
bottomName = "bottom"

-- | The bottom pattern
bottomP :: Pattern
bottomP = pcon0 bottomName

-- | The bottom expression
bottom :: Expr
bottom = con0 bottomName

