module Main(main) where

import Test.Tasty
import qualified TestSuite.Arrays.Memory

main :: IO ()
main = defaultMain (testGroup "Tests" tests)

tests :: [TestTree]
tests =
  [ TestSuite.Arrays.Memory.tests ]
