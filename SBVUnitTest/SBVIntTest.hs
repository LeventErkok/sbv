module Main(main) where

import Test.Tasty
import qualified TestSuite.Arrays.Memory
import qualified TestSuite.Basics.ArithSolver
import qualified TestSuite.Basics.Higher
import qualified TestSuite.Basics.Index
import qualified TestSuite.Basics.ProofTests
import qualified TestSuite.Basics.QRem
import qualified TestSuite.BitPrecise.BitTricks
import qualified TestSuite.BitPrecise.PrefixSum
import qualified TestSuite.CRC.CCITT_Unidir
import qualified TestSuite.CRC.USB5
import qualified TestSuite.CRC.GenPoly
import qualified TestSuite.Crypto.RC4
import qualified TestSuite.Polynomials.Polynomials
import qualified TestSuite.CRC.Parity
import qualified TestSuite.Puzzles.MagicSquare
import qualified TestSuite.Puzzles.NQueens
import qualified TestSuite.Puzzles.PowerSet
import qualified TestSuite.Puzzles.Sudoku
import qualified TestSuite.Uninterpreted.Axioms
import qualified TestSuite.Uninterpreted.Function
import qualified TestSuite.Uninterpreted.Sort
import qualified TestSuite.Uninterpreted.Uninterpreted

main :: IO ()
main = defaultMain (testGroup "Tests" tests)

tests :: [TestTree]
tests =
  [ TestSuite.Arrays.Memory.tests
  , TestSuite.Basics.ArithSolver.tests
  , TestSuite.Basics.Higher.tests
  , TestSuite.Basics.Index.tests
  -- ite
  , TestSuite.Basics.ProofTests.tests
  , TestSuite.Basics.QRem.tests
  , TestSuite.BitPrecise.BitTricks.tests
  , TestSuite.BitPrecise.PrefixSum.tests
  , TestSuite.CRC.CCITT_Unidir.tests
  , TestSuite.CRC.USB5.tests
  , TestSuite.CRC.GenPoly.tests
  , TestSuite.Crypto.RC4.tests
  , TestSuite.Polynomials.Polynomials.tests
  , TestSuite.CRC.Parity.tests
  -- dogcat
  -- euler
  , TestSuite.Puzzles.MagicSquare.tests
  , TestSuite.Puzzles.NQueens.tests
  , TestSuite.Puzzles.PowerSet.tests
  , TestSuite.Puzzles.Sudoku.tests
  -- temp
  -- u2br
  -- auf
  , TestSuite.Uninterpreted.Axioms.tests
  , TestSuite.Uninterpreted.Function.tests
  , TestSuite.Uninterpreted.Sort.tests
  , TestSuite.Uninterpreted.Uninterpreted.tests
  ]
