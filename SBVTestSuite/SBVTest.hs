{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Test.Tasty
import Test.Tasty.Runners (noPattern, TestPattern)

import qualified TestSuite.Arrays.Memory
import qualified TestSuite.Basics.AllSat
import qualified TestSuite.Basics.ArithNoSolver
import qualified TestSuite.Basics.ArithSolver
import qualified TestSuite.Basics.BasicTests
import qualified TestSuite.Basics.GenBenchmark
import qualified TestSuite.Basics.Higher
import qualified TestSuite.Basics.Index
import qualified TestSuite.Basics.IteTest
import qualified TestSuite.Basics.ProofTests
import qualified TestSuite.Basics.PseudoBoolean
import qualified TestSuite.Basics.QRem
import qualified TestSuite.Basics.Quantifiers
import qualified TestSuite.Basics.SquashReals
import qualified TestSuite.Basics.TOut
import qualified TestSuite.BitPrecise.BitTricks
import qualified TestSuite.BitPrecise.Legato
import qualified TestSuite.BitPrecise.MergeSort
import qualified TestSuite.BitPrecise.PrefixSum
import qualified TestSuite.CodeGeneration.AddSub
import qualified TestSuite.CodeGeneration.CgTests
import qualified TestSuite.CodeGeneration.CRC_USB5
import qualified TestSuite.CodeGeneration.Fibonacci
import qualified TestSuite.CodeGeneration.Floats
import qualified TestSuite.CodeGeneration.GCD
import qualified TestSuite.CodeGeneration.PopulationCount
import qualified TestSuite.CodeGeneration.Uninterpreted
import qualified TestSuite.CRC.CCITT
import qualified TestSuite.CRC.CCITT_Unidir
import qualified TestSuite.CRC.GenPoly
import qualified TestSuite.CRC.Parity
import qualified TestSuite.CRC.USB5
import qualified TestSuite.Crypto.AES
import qualified TestSuite.Crypto.RC4
import qualified TestSuite.Existentials.CRCPolynomial
import qualified TestSuite.GenTest.GenTests
import qualified TestSuite.Optimization.AssertSoft
import qualified TestSuite.Optimization.Basics
import qualified TestSuite.Optimization.Combined
import qualified TestSuite.Optimization.ExtensionField
import qualified TestSuite.Optimization.Reals
import qualified TestSuite.Polynomials.Polynomials
import qualified TestSuite.Puzzles.Coins
import qualified TestSuite.Puzzles.Counts
import qualified TestSuite.Puzzles.DogCatMouse
import qualified TestSuite.Puzzles.Euler185
import qualified TestSuite.Puzzles.MagicSquare
import qualified TestSuite.Puzzles.NQueens
import qualified TestSuite.Puzzles.PowerSet
import qualified TestSuite.Puzzles.Sudoku
import qualified TestSuite.Puzzles.Temperature
import qualified TestSuite.Puzzles.U2Bridge
import qualified TestSuite.Queries.BasicQuery
import qualified TestSuite.Queries.Int_ABC
import qualified TestSuite.Queries.Int_Boolector
import qualified TestSuite.Queries.Int_CVC4
import qualified TestSuite.Queries.Int_Mathsat
import qualified TestSuite.Queries.Int_Yices
import qualified TestSuite.Queries.Int_Z3
import qualified TestSuite.Uninterpreted.AUF
import qualified TestSuite.Uninterpreted.Axioms
import qualified TestSuite.Uninterpreted.Function
import qualified TestSuite.Uninterpreted.Sort
import qualified TestSuite.Uninterpreted.Uninterpreted

main :: IO ()
main = defaultMain $ askOption $ \(v :: TestPattern) -> testGroup "Tests" (pick v)
 where pick v
        | show v == show noPattern = [t | (False, t) <- allTests]  -- Running in travis, just run no-solver tests
        | True                     = [t | (_,     t) <- allTests]  -- Running locally, run everthing

-- If the Bool is True, then that test requires the presence of Z3
-- Otherwise, it can be run without the presence of the solver.
allTests :: [(Bool, TestTree)]
allTests = [ (True,  TestSuite.Arrays.Memory.tests)
           , (True,  TestSuite.Basics.AllSat.tests)
           , (False, TestSuite.Basics.ArithNoSolver.tests)
           , (True,  TestSuite.Basics.ArithSolver.tests)
           , (False, TestSuite.Basics.BasicTests.tests)
           , (False, TestSuite.Basics.GenBenchmark.tests)
           , (True,  TestSuite.Basics.Higher.tests)
           , (True,  TestSuite.Basics.Index.tests)
           , (True,  TestSuite.Basics.IteTest.tests)
           , (True,  TestSuite.Basics.ProofTests.tests)
           , (True,  TestSuite.Basics.PseudoBoolean.tests)
           , (True,  TestSuite.Basics.QRem.tests)
           , (True,  TestSuite.Basics.Quantifiers.tests)
           , (True,  TestSuite.Basics.SquashReals.tests)
           , (True,  TestSuite.Basics.TOut.tests)
           , (True,  TestSuite.BitPrecise.BitTricks.tests)
           , (False, TestSuite.BitPrecise.Legato.tests)
           , (False, TestSuite.BitPrecise.MergeSort.tests)
           , (True,  TestSuite.BitPrecise.PrefixSum.tests)
           , (False, TestSuite.CodeGeneration.AddSub.tests)
           , (False, TestSuite.CodeGeneration.CgTests.tests)
           , (False, TestSuite.CodeGeneration.CRC_USB5.tests)
           , (False, TestSuite.CodeGeneration.Fibonacci.tests)
           , (False, TestSuite.CodeGeneration.Floats.tests)
           , (False, TestSuite.CodeGeneration.GCD.tests)
           , (False, TestSuite.CodeGeneration.PopulationCount.tests)
           , (False, TestSuite.CodeGeneration.Uninterpreted.tests)
           , (False, TestSuite.CRC.CCITT.tests)
           , (True,  TestSuite.CRC.CCITT_Unidir.tests)
           , (True,  TestSuite.CRC.GenPoly.tests)
           , (True,  TestSuite.CRC.Parity.tests)
           , (True,  TestSuite.CRC.USB5.tests)
           , (False, TestSuite.Crypto.AES.tests)
           , (True,  TestSuite.Crypto.RC4.tests)
           , (False, TestSuite.Existentials.CRCPolynomial.tests)
           , (False, TestSuite.GenTest.GenTests.tests)
           , (True,  TestSuite.Optimization.AssertSoft.tests)
           , (True,  TestSuite.Optimization.Basics.tests)
           , (True,  TestSuite.Optimization.Combined.tests)
           , (True,  TestSuite.Optimization.ExtensionField.tests)
           , (True,  TestSuite.Optimization.Reals.tests)
           , (True,  TestSuite.Polynomials.Polynomials.tests)
           , (False, TestSuite.Puzzles.Coins.tests)
           , (False, TestSuite.Puzzles.Counts.tests)
           , (True,  TestSuite.Puzzles.DogCatMouse.tests)
           , (True,  TestSuite.Puzzles.Euler185.tests)
           , (True,  TestSuite.Puzzles.MagicSquare.tests)
           , (True,  TestSuite.Puzzles.NQueens.tests)
           , (True,  TestSuite.Puzzles.PowerSet.tests)
           , (True,  TestSuite.Puzzles.Sudoku.tests)
           , (True,  TestSuite.Puzzles.Temperature.tests)
           , (True,  TestSuite.Puzzles.U2Bridge.tests)
           , (True,  TestSuite.Queries.BasicQuery.tests)
           , (True,  TestSuite.Queries.Int_ABC.tests)
           , (True,  TestSuite.Queries.Int_Boolector.tests)
           , (True,  TestSuite.Queries.Int_CVC4.tests)
           , (True,  TestSuite.Queries.Int_Mathsat.tests)
           , (True,  TestSuite.Queries.Int_Yices.tests)
           , (True,  TestSuite.Queries.Int_Z3.tests)
           , (True,  TestSuite.Uninterpreted.AUF.tests)
           , (True,  TestSuite.Uninterpreted.Axioms.tests)
           , (True,  TestSuite.Uninterpreted.Function.tests)
           , (True,  TestSuite.Uninterpreted.Sort.tests)
           , (True,  TestSuite.Uninterpreted.Uninterpreted.tests)
           ]
