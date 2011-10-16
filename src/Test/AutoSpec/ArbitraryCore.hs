{-# LANGUAGE TypeSynonymInstances #-}
module Test.AutoSpec.ArbitraryCore where

-- Orphan instances for the rescue!

import Test.AutoSpec.Core
import Test.QuickCheck
import Data.Char
import Control.Monad
import Control.Applicative

instance Arbitrary k => Arbitrary (Pattern k) where
    arbitrary = sized $ \s -> frequency
         [(5        ,PVar <$> arbName)
         ,(s `div` 2,(`PCons` [])                  <$> arbC 0)
         ,(s `div` 3,(\n x -> PCons n [x])         <$> arbC 1 <*> arbitrary)
         ,(s `div` 4,(\n x y -> PCons n [x,y])     <$> arbC 2 <*> arbitrary <*> arbitrary)
         ,(s `div` 5,(\n x y z -> PCons n [x,y,z]) <$> arbC 3 <*> arbitrary <*> arbitrary <*> arbitrary)
         ]
                
arbPat s = frequency 
         [(5        ,PVar <$> arbName)
         ,(s `div` 2,(`PCons` [])                           <$> arbC 0)
         ,(s `div` 3,(\n x -> PCons n [NP x])               <$> arbC 1 <*> arbPat s')
         ,(s `div` 4,(\n x y -> PCons n [NP x,NP y])        <$> arbC 2 <*> arbPat s' <*> arbPat s')
         ,(s `div` 5,(\n x y z -> PCons n [NP x,NP y,NP z]) <$> arbC 3 <*> arbPat s' <*> arbPat s' <*> arbitrary)
         ]
  where s' = s `div` 2
             
instance Arbitrary Name where
    arbitrary = arbName

instance Arbitrary NestedPat where
    arbitrary = sized $ \s -> NP <$> arbPat s

names = map return "abcxyz"

arbName = elements names

arbC n = elements (map ((++ show n) . map toUpper) names)

instance Arbitrary k => Arbitrary (Decl k) where
    arbitrary = Fun <$> arbName <*> args <*> arbitrary
        where args = choose (0,3) >>= flip replicateM arbitrary

instance Arbitrary k => Arbitrary (Expr k) where
    arbitrary = sized arbExpr

arbExpr :: Arbitrary k => Int -> Gen (Expr k)
arbExpr s = frequency 
          [(s,do l <- choose (1,4)
                 Case <$> arbName <*> replicateM l (arbBranch (s `div` 2)))
          ,(s,app <$> arbExpr s' <*> arbExpr s')
          ,(s `div` 2,(`Cons` [])                  <$> arbC 0)
          ,(s `div` 3,(\n x -> Cons n [x])         <$> arbC 1 <*> arbExpr s')
          ,(s `div` 4,(\n x y -> Cons n [x,y])     <$> arbC 2 <*> arbExpr s' <*> arbExpr s')
          ,(s `div` 5,(\n x y z -> Cons n [x,y,z]) <$> arbC 3 <*> arbExpr s' <*> arbExpr s' <*> arbExpr s')
          ,(5,Var <$> arbName)
          ,(1,return Fail)
          ]            
  where s' = s `div` 2

arbBranch s = Branch <$> arbitrary <*> arbExpr s