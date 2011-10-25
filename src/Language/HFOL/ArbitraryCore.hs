{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, UndecidableInstances #-}
module Language.HFOL.ArbitraryCore where

-- Orphan instances for the rescue!

import Language.HFOL.Bottom
import Language.HFOL.Core
import Test.QuickCheck
import Data.Char
import Control.Monad
import Control.Applicative

names :: [String]
names = map return "abcxyz"

arbName :: Gen Name
arbName = elements names

arbC :: Int -> Gen Name
arbC n = elements (map ((++ show n) . map toUpper) names)

instance Arbitrary Pattern where
    arbitrary = sized (arbPat False)
    shrink PWild    = []
    shrink (PVar _) = []
    shrink (PCon c as) = as ++ [PCon c as' | as' <- mapM shrink as]

newtype BottomPattern = BP { unBP :: Pattern } deriving (Eq)

instance Show Pattern => Show BottomPattern where
   show (BP p) = show p

instance Arbitrary BottomPattern where
    arbitrary = BP <$> sized (arbPat True)

arbPat :: Bool -> Int -> Gen Pattern
arbPat bottoms s = frequency
                 [(5,PVar <$> arbName)
                 ,(if bottoms then 5 else 0,return bottomP)
                 ,(1,return PWild)
                 ,(s,do n <- choose (0,2)
                        PCon <$> arbC n <*> replicateM n (arbPat bottoms s'))
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

instance Arbitrary Expr where
    arbitrary = sized arbExpr

arbExpr :: Int -> Gen Expr
arbExpr s = frequency
          [(5,Var <$> arbName)
          ,(s,app <$> arbExpr s' <*> arbExpr s')
          ,(s,do n <- choose (0,4)
                 Con <$> arbC n <*> replicateM n (arbExpr s'))
          ]
  where s' = s `div` 2

instance Arbitrary Branch where
  arbitrary = (:->) <$> arbitrary <*> (Var <$> arbName)

arbBranch :: Int -> Gen Branch
arbBranch s = (:->) <$> arbPat False s <*> arbExpr s