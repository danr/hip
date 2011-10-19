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
