{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Test.Tasty
import System.Environment (lookupEnv)

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
import qualified TestSuite.Queries.Enums
import qualified TestSuite.Queries.FreshVars
import qualified TestSuite.Queries.Int_ABC
import qualified TestSuite.Queries.Int_Boolector
import qualified TestSuite.Queries.Int_CVC4
import qualified TestSuite.Queries.Int_Mathsat
import qualified TestSuite.Queries.Int_Yices
import qualified TestSuite.Queries.Int_Z3
import qualified TestSuite.Queries.Uninterpreted
import qualified TestSuite.Uninterpreted.AUF
import qualified TestSuite.Uninterpreted.Axioms
import qualified TestSuite.Uninterpreted.Function
import qualified TestSuite.Uninterpreted.Sort
import qualified TestSuite.Uninterpreted.Uninterpreted

main :: IO ()
main = do mbTravis <- lookupEnv "SBV_UNDER_TRAVIS"

          isTravis <- case mbTravis of
                        Just "yes" -> do putStrLn "SBVTests: Running on Travis"
                                         return True
                        _          -> do putStrLn "SBVTests: Not running on Travis"
                                         return False

          let testCases = [tc | (canRunOnTravis, _, tc) <- allTests, not isTravis || canRunOnTravis]

          defaultMain $ testGroup "Tests" testCases

-- If the first  Bool is True, then that test can run on Travis
-- If the second Bool is True, then that test requires the presence of Z3
-- Note that we currently do not use the second boolean, but it can come in handy later.
allTests :: [(Bool, Bool, TestTree)]
allTests = [ (True,  True,  TestSuite.Arrays.Memory.tests)
           , (True,  True,  TestSuite.Basics.AllSat.tests)
           , (True,  False, TestSuite.Basics.ArithNoSolver.tests)
           , (True,  True,  TestSuite.Basics.ArithSolver.tests)
           , (True,  False, TestSuite.Basics.BasicTests.tests)
           , (True,  False, TestSuite.Basics.GenBenchmark.tests)
           , (True,  True,  TestSuite.Basics.Higher.tests)
           , (True,  True,  TestSuite.Basics.Index.tests)
           , (True,  True,  TestSuite.Basics.IteTest.tests)
           , (True,  True,  TestSuite.Basics.ProofTests.tests)
           , (True,  True,  TestSuite.Basics.PseudoBoolean.tests)
           , (True,  True,  TestSuite.Basics.QRem.tests)
           , (True,  True,  TestSuite.Basics.Quantifiers.tests)
           , (True,  True,  TestSuite.Basics.SquashReals.tests)
           , (True,  True,  TestSuite.Basics.TOut.tests)
           , (True,  True,  TestSuite.BitPrecise.BitTricks.tests)
           , (True,  False, TestSuite.BitPrecise.Legato.tests)
           , (True,  False, TestSuite.BitPrecise.MergeSort.tests)
           , (True,  True,  TestSuite.BitPrecise.PrefixSum.tests)
           , (True,  False, TestSuite.CodeGeneration.AddSub.tests)
           , (True,  False, TestSuite.CodeGeneration.CgTests.tests)
           , (True,  False, TestSuite.CodeGeneration.CRC_USB5.tests)
           , (True,  False, TestSuite.CodeGeneration.Fibonacci.tests)
           , (True,  False, TestSuite.CodeGeneration.Floats.tests)
           , (True,  False, TestSuite.CodeGeneration.GCD.tests)
           , (True,  False, TestSuite.CodeGeneration.PopulationCount.tests)
           , (True,  False, TestSuite.CodeGeneration.Uninterpreted.tests)
           , (True,  False, TestSuite.CRC.CCITT.tests)
           , (True,  True,  TestSuite.CRC.CCITT_Unidir.tests)
           , (True,  True,  TestSuite.CRC.GenPoly.tests)
           , (True,  True,  TestSuite.CRC.Parity.tests)
           , (True,  True,  TestSuite.CRC.USB5.tests)
           , (True,  False, TestSuite.Crypto.AES.tests)
           , (True,  True,  TestSuite.Crypto.RC4.tests)
           , (True,  False, TestSuite.Existentials.CRCPolynomial.tests)
           , (True,  False, TestSuite.GenTest.GenTests.tests)
           , (True,  True,  TestSuite.Optimization.AssertSoft.tests)
           , (True,  True,  TestSuite.Optimization.Basics.tests)
           , (True,  True,  TestSuite.Optimization.Combined.tests)
           , (True,  True,  TestSuite.Optimization.ExtensionField.tests)
           , (True,  True,  TestSuite.Optimization.Reals.tests)
           , (True,  True,  TestSuite.Polynomials.Polynomials.tests)
           , (True,  False, TestSuite.Puzzles.Coins.tests)
           , (True,  False, TestSuite.Puzzles.Counts.tests)
           , (True,  True,  TestSuite.Puzzles.DogCatMouse.tests)
           , (True,  True,  TestSuite.Puzzles.Euler185.tests)
           , (True,  True,  TestSuite.Puzzles.MagicSquare.tests)
           , (True,  True,  TestSuite.Puzzles.NQueens.tests)
           , (True,  True,  TestSuite.Puzzles.PowerSet.tests)
           , (True,  True,  TestSuite.Puzzles.Sudoku.tests)
           , (True,  True,  TestSuite.Puzzles.Temperature.tests)
           , (True,  True,  TestSuite.Puzzles.U2Bridge.tests)
           , (False, True,  TestSuite.Queries.BasicQuery.tests)
           , (True,  True,  TestSuite.Queries.Enums.tests)
           , (True,  True,  TestSuite.Queries.FreshVars.tests)
           , (False, True,  TestSuite.Queries.Int_ABC.tests)
           , (False, True,  TestSuite.Queries.Int_Boolector.tests)
           , (False, True,  TestSuite.Queries.Int_CVC4.tests)
           , (False, True,  TestSuite.Queries.Int_Mathsat.tests)
           , (False, True,  TestSuite.Queries.Int_Yices.tests)
           , (True,  True,  TestSuite.Queries.Int_Z3.tests)
           , (True,  True,  TestSuite.Queries.Uninterpreted.tests)
           , (True,  True,  TestSuite.Uninterpreted.AUF.tests)
           , (True,  True,  TestSuite.Uninterpreted.Axioms.tests)
           , (True,  True,  TestSuite.Uninterpreted.Function.tests)
           , (True,  True,  TestSuite.Uninterpreted.Sort.tests)
           , (True,  True,  TestSuite.Uninterpreted.Uninterpreted.tests)
           ]
