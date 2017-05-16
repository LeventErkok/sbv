module Main(main) where

import Test.Tasty
import qualified TestSuite.Arrays.Memory
import qualified TestSuite.Basics.Index
import qualified TestSuite.Basics.ProofTests
import qualified TestSuite.Basics.QRem

main :: IO ()
main = defaultMain (testGroup "Tests" tests)

tests :: [TestTree]
tests =
  [ TestSuite.Arrays.Memory.tests
  -- arith
  -- higher
  , TestSuite.Basics.Index.tests
  -- ite
  , TestSuite.Basics.ProofTests.tests
  , TestSuite.Basics.QRem.tests
  ]
