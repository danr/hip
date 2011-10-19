module Language.HFOL.Test where

import Language.HFOL.Core
import Language.HFOL.Parser
import Language.HFOL.Pretty

import Language.HFOL.ArbitraryCore
import Test.QuickCheck

import System.IO.Unsafe

prop_parsePretty :: Decl -> Bool
prop_parsePretty e = unsafePerformIO $ do
  putStrLn $ prettyCore e
  return $ (either (const False) (const True) . extParser . prettyCore) e

prop_parsePrettyEq :: Decl -> Bool
prop_parsePrettyEq e = unsafePerformIO $ do
--  putStrLn $ prettyCore e
--  print $ e
--  print $ extParser $ prettyCore e
  return $ (either (const False) (\[x] -> x == e) . extParser . prettyCore) e