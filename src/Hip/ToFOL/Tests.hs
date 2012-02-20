module Hip.ToFOL.Test where

import Hip.ToFOL.Core
import Hip.ToFOL.Parser
import Hip.ToFOL.Pretty

import Hip.ToFOL.ArbitraryCore
import Test.QuickCheck

import System.IO.Unsafe

prop_parsePretty :: Decl -> Bool
prop_parsePretty e = unsafePerformIO $ do
  putStrLn $ prettyCore e
  return $ (either (const False) (const True) . extParser . prettyCore) e

prop_parsePrettyEq :: Decl -> Bool
prop_parsePrettyEq e = unsafePerformIO $ do
  putStrLn $ prettyCore e
  print e
  print $ extParser $ prettyCore e
  return $ (either (const False) (\[x] -> x == e) . extParser . prettyCore) e