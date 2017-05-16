module Main(main) where

import Test.Tasty
import qualified TestSuite.Arrays.Memory
import qualified TestSuite.Basics.Index

main :: IO ()
main = defaultMain (testGroup "Tests" tests)

tests :: [TestTree]
tests =
  [ TestSuite.Arrays.Memory.tests
  , TestSuite.Basics.Index.tests
  ]
