module Test.AutoSpec.Test where

import Test.AutoSpec.Core
import Test.AutoSpec.Parser
import Test.AutoSpec.Pretty

import Test.AutoSpec.ArbitraryCore
import Test.QuickCheck

import System.IO.Unsafe
                     
prop_parsePretty :: ExtDecl -> Bool
prop_parsePretty e = unsafePerformIO $ do
--  putStrLn $ prettyCore e
  return $ (either (const False) (const True) . extParser . prettyCore) e

prop_parsePrettyEq :: ExtDecl -> Bool
prop_parsePrettyEq e = unsafePerformIO $ do
--  putStrLn $ prettyCore e
--  print $ e
--  print $ extParser $ prettyCore e
  return $ (either (const False) (\[x] -> x == e) . extParser . prettyCore) e