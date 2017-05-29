module Main(main) where

import Test.Tasty
import qualified TestSuite.Arrays.Memory
import qualified TestSuite.Basics.Index
import qualified TestSuite.Basics.ProofTests
import qualified TestSuite.Basics.QRem
import qualified TestSuite.BitPrecise.BitTricks
import qualified TestSuite.BitPrecise.PrefixSum
import qualified TestSuite.CRC.CCITT_Unidir
import qualified TestSuite.CRC.GenPoly
import qualified TestSuite.Crypto.RC4
import qualified TestSuite.Polynomials.Polynomials

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
  , TestSuite.BitPrecise.BitTricks.tests
  , TestSuite.BitPrecise.PrefixSum.tests
  , TestSuite.CRC.CCITT_Unidir.tests
  , TestSuite.CRC.GenPoly.tests
  , TestSuite.Crypto.RC4.tests
  , TestSuite.Polynomials.Polynomials.tests
  ]
