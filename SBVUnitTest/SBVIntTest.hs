{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Test.Tasty
import Test.Tasty.Runners (noPattern, TestPattern)
import qualified TestSuite.Arrays.Memory
import qualified TestSuite.Basics.ArithSolver
import qualified TestSuite.Basics.Higher
import qualified TestSuite.Basics.Index
import qualified TestSuite.Basics.IteTest
import qualified TestSuite.Basics.ProofTests
import qualified TestSuite.Basics.QRem
import qualified TestSuite.Basics.AllSat
import qualified TestSuite.Basics.TOut
import qualified TestSuite.BitPrecise.BitTricks
import qualified TestSuite.BitPrecise.PrefixSum
import qualified TestSuite.CRC.CCITT_Unidir
import qualified TestSuite.CRC.USB5
import qualified TestSuite.CRC.GenPoly
import qualified TestSuite.Crypto.RC4
import qualified TestSuite.Polynomials.Polynomials
import qualified TestSuite.CRC.Parity
import qualified TestSuite.Puzzles.DogCatMouse
import qualified TestSuite.Puzzles.Euler185
import qualified TestSuite.Puzzles.MagicSquare
import qualified TestSuite.Puzzles.NQueens
import qualified TestSuite.Puzzles.PowerSet
import qualified TestSuite.Puzzles.Sudoku
import qualified TestSuite.Puzzles.Temperature
import qualified TestSuite.Puzzles.U2Bridge
import qualified TestSuite.Uninterpreted.AUF
import qualified TestSuite.Uninterpreted.Axioms
import qualified TestSuite.Uninterpreted.Function
import qualified TestSuite.Uninterpreted.Sort
import qualified TestSuite.Uninterpreted.Uninterpreted
import qualified TestSuite.Optimization.Basics
import qualified TestSuite.Optimization.ExtensionField
import qualified TestSuite.Optimization.AssertSoft
import qualified TestSuite.Optimization.Combined
import qualified TestSuite.Optimization.Reals
import qualified TestSuite.Queries.BasicQuery
import qualified TestSuite.Queries.Int_ABC
import qualified TestSuite.Queries.Int_Boolector
import qualified TestSuite.Queries.Int_CVC4
import qualified TestSuite.Queries.Int_Mathsat
import qualified TestSuite.Queries.Int_Yices
import qualified TestSuite.Queries.Int_Z3

main :: IO ()
main =
  defaultMain
    (askOption
      (\(v :: TestPattern) ->
        testGroup
          "Tests"
          (if show v == show noPattern
             then []
             else tests)))

tests :: [TestTree]
tests =
  [ TestSuite.Arrays.Memory.tests
  , TestSuite.Basics.ArithSolver.tests
  , TestSuite.Basics.Higher.tests
  , TestSuite.Basics.Index.tests
  , TestSuite.Basics.IteTest.tests
  , TestSuite.Basics.ProofTests.tests
  , TestSuite.Basics.QRem.tests
  , TestSuite.Basics.AllSat.tests
  , TestSuite.Basics.TOut.tests
  , TestSuite.BitPrecise.BitTricks.tests
  , TestSuite.BitPrecise.PrefixSum.tests
  , TestSuite.CRC.CCITT_Unidir.tests
  , TestSuite.CRC.USB5.tests
  , TestSuite.CRC.GenPoly.tests
  , TestSuite.Crypto.RC4.tests
  , TestSuite.Polynomials.Polynomials.tests
  , TestSuite.CRC.Parity.tests
  , TestSuite.Puzzles.DogCatMouse.tests
  , TestSuite.Puzzles.Euler185.tests
  , TestSuite.Puzzles.MagicSquare.tests
  , TestSuite.Puzzles.NQueens.tests
  , TestSuite.Puzzles.PowerSet.tests
  , TestSuite.Puzzles.Sudoku.tests
  , TestSuite.Puzzles.Temperature.tests
  , TestSuite.Puzzles.U2Bridge.tests
  , TestSuite.Uninterpreted.AUF.tests
  , TestSuite.Uninterpreted.Axioms.tests
  , TestSuite.Uninterpreted.Function.tests
  , TestSuite.Uninterpreted.Sort.tests
  , TestSuite.Uninterpreted.Uninterpreted.tests
  , TestSuite.Optimization.Basics.tests
  , TestSuite.Optimization.ExtensionField.tests
  , TestSuite.Optimization.AssertSoft.tests
  , TestSuite.Optimization.Combined.tests
  , TestSuite.Optimization.Reals.tests
  , TestSuite.Queries.BasicQuery.tests
  , TestSuite.Queries.Int_ABC.tests
  , TestSuite.Queries.Int_Boolector.tests
  , TestSuite.Queries.Int_CVC4.tests
  , TestSuite.Queries.Int_Mathsat.tests
  , TestSuite.Queries.Int_Yices.tests
  , TestSuite.Queries.Int_Z3.tests
  ]
