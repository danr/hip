{-# LANGUAGE TypeSynonymInstances #-}
module Language.HFOL.ArbitraryCore where

-- Orphan instances for the rescue!

import Language.HFOL.Core
import Test.QuickCheck
import Data.Char
import Control.Monad
import Control.Applicative

names = map return "abcxyz"

arbName = elements names

arbC n = elements (map ((++ show n) . map toUpper) names)

instance Arbitrary Pattern where
    arbitrary = sized arbPat
    shrink (PVar _) = []
    shrink (PCon c as) = as ++ [PCon c as' | as' <- sequence (map shrink as)]


arbPat s = frequency
         [(5,PVar <$> arbName)
         ,(1,return (PVar "_"))
         ,(s,do n <- choose (0,2)
                PCon <$> arbC n <*> replicateM n (arbPat s'))
         ]
  where s' = s `div` 2

instance Arbitrary Decl where
    arbitrary = Func <$> arbName <*> args <*> arbitrary
        where args = choose (0,3) >>= flip replicateM arbName

instance Arbitrary Body where
    arbitrary = sized $ \s -> oneof
              [ do n <- choose (1,4)
                   brs <- replicateM n (arbBranch s)
                   e <- arbExpr s
                   return (Case e brs)
              , Expr <$> arbExpr s
              ]

arbExpr s = frequency
          [(5,Var <$> arbName)
          ,(s,app <$> arbExpr s' <*> arbExpr s')
          ,(s,do n <- choose (0,4)
                 Con <$> arbC n <*> replicateM n (arbExpr s'))
          ]
  where s' = s `div` 2

instance Arbitrary Branch where
  arbitrary = (:->) <$> arbitrary <*> (Var <$> arbName)

arbBranch s = (:->) <$> arbPat s <*> arbExpr s