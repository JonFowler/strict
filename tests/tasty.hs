module Main where

import Test.Tasty
import Test.Tasty.QuickCheck
import Projection

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "(checked by Quickcheck)"
  [ testProperty "(5+) == (5+)" $
     \x -> ( (x :: Int) + 5) == (x+5)

  ]
