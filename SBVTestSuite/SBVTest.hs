{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Test.Tasty

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..), TravisOS(..), pickTests)

import System.Exit (exitSuccess)

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
import qualified TestSuite.Basics.Recursive
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
import qualified TestSuite.Queries.BadOption
import qualified TestSuite.Queries.Enums
import qualified TestSuite.Queries.FreshVars
import qualified TestSuite.Queries.Int_ABC
import qualified TestSuite.Queries.Int_Boolector
import qualified TestSuite.Queries.Int_CVC4
import qualified TestSuite.Queries.Int_Mathsat
import qualified TestSuite.Queries.Int_Yices
import qualified TestSuite.Queries.Int_Z3
import qualified TestSuite.Queries.Interpolants
import qualified TestSuite.Queries.Uninterpreted
import qualified TestSuite.Uninterpreted.AUF
import qualified TestSuite.Uninterpreted.Axioms
import qualified TestSuite.Uninterpreted.Function
import qualified TestSuite.Uninterpreted.Sort
import qualified TestSuite.Uninterpreted.Uninterpreted

-- On Travis, the build machines are subject to time-out limits. So, we cannot really run
-- everything yet remain within the timeout bounds. Here, we randomly pick a subset; with
-- the hope that over many runs this tests larger parts of the test-suite.
travisFilter :: TravisOS -> TestTree -> IO TestTree
travisFilter te tt = do putStrLn $ "Travis: Reducing tests by " ++ show (100-p) ++ "% for running on " ++ show te
                        pickTests p tt
  where p = case te of
              TravisLinux   ->  30
              TravisOSX     ->  10
              TravisWindows -> 100   -- Travis doesn't actually have Windows, just keep this at 100 for now.

main :: IO ()
main = do testEnv <- getTestEnvironment

          putStrLn $ "SBVTest: Test platform: " ++ show testEnv

          let allTestCases       = testGroup "Tests" [tc | (_,    tc) <- allTests]
              allTravisTestCases = testGroup "Tests" [tc | (True, tc) <- allTests]

          case testEnv of
            TestEnvLocal     -> defaultMain allTestCases
            TestEnvTravis os -> defaultMain =<< travisFilter os allTravisTestCases
            TestEnvUnknown   -> do putStrLn "Unknown test environment, skipping tests"
                                   exitSuccess

-- If the first  Bool is True, then that test can run on Travis
allTests :: [(Bool, TestTree)]
allTests = [ (True,  TestSuite.Arrays.Memory.tests)
           , (True,  TestSuite.Basics.AllSat.tests)
           , (True,  TestSuite.Basics.ArithNoSolver.tests)
           , (True,  TestSuite.Basics.ArithSolver.tests)
           , (True,  TestSuite.Basics.BasicTests.tests)
           , (True,  TestSuite.Basics.GenBenchmark.tests)
           , (True,  TestSuite.Basics.Higher.tests)
           , (True,  TestSuite.Basics.Index.tests)
           , (True,  TestSuite.Basics.IteTest.tests)
           , (True,  TestSuite.Basics.ProofTests.tests)
           , (True,  TestSuite.Basics.PseudoBoolean.tests)
           , (True,  TestSuite.Basics.QRem.tests)
           , (True,  TestSuite.Basics.Quantifiers.tests)
           , (True,  TestSuite.Basics.Recursive.tests)
           , (True,  TestSuite.Basics.SquashReals.tests)
           , (True,  TestSuite.Basics.TOut.tests)
           , (True,  TestSuite.BitPrecise.BitTricks.tests)
           , (True,  TestSuite.BitPrecise.Legato.tests)
           , (True,  TestSuite.BitPrecise.MergeSort.tests)
           , (True,  TestSuite.BitPrecise.PrefixSum.tests)
           , (True,  TestSuite.CodeGeneration.AddSub.tests)
           , (True,  TestSuite.CodeGeneration.CgTests.tests)
           , (True,  TestSuite.CodeGeneration.CRC_USB5.tests)
           , (True,  TestSuite.CodeGeneration.Fibonacci.tests)
           , (True,  TestSuite.CodeGeneration.Floats.tests)
           , (True,  TestSuite.CodeGeneration.GCD.tests)
           , (True,  TestSuite.CodeGeneration.PopulationCount.tests)
           , (True,  TestSuite.CodeGeneration.Uninterpreted.tests)
           , (True,  TestSuite.CRC.CCITT.tests)
           , (True,  TestSuite.CRC.CCITT_Unidir.tests)
           , (True,  TestSuite.CRC.GenPoly.tests)
           , (True,  TestSuite.CRC.Parity.tests)
           , (True,  TestSuite.CRC.USB5.tests)
           , (True,  TestSuite.Crypto.AES.tests)
           , (True,  TestSuite.Crypto.RC4.tests)
           , (True,  TestSuite.Existentials.CRCPolynomial.tests)
           , (True,  TestSuite.GenTest.GenTests.tests)
           , (True,  TestSuite.Optimization.AssertSoft.tests)
           , (True,  TestSuite.Optimization.Basics.tests)
           , (True,  TestSuite.Optimization.Combined.tests)
           , (True,  TestSuite.Optimization.ExtensionField.tests)
           , (True,  TestSuite.Optimization.Reals.tests)
           , (True,  TestSuite.Polynomials.Polynomials.tests)
           , (True,  TestSuite.Puzzles.Coins.tests)
           , (True,  TestSuite.Puzzles.Counts.tests)
           , (True,  TestSuite.Puzzles.DogCatMouse.tests)
           , (True,  TestSuite.Puzzles.Euler185.tests)
           , (True,  TestSuite.Puzzles.MagicSquare.tests)
           , (True,  TestSuite.Puzzles.NQueens.tests)
           , (True,  TestSuite.Puzzles.PowerSet.tests)
           , (True,  TestSuite.Puzzles.Sudoku.tests)
           , (True,  TestSuite.Puzzles.Temperature.tests)
           , (True,  TestSuite.Puzzles.U2Bridge.tests)
           , (False, TestSuite.Queries.BasicQuery.tests)
           , (False, TestSuite.Queries.BadOption.tests)
           , (True,  TestSuite.Queries.Enums.tests)
           , (True,  TestSuite.Queries.FreshVars.tests)
           , (False, TestSuite.Queries.Int_ABC.tests)
           , (False, TestSuite.Queries.Int_Boolector.tests)
           , (False, TestSuite.Queries.Int_CVC4.tests)
           , (False, TestSuite.Queries.Int_Mathsat.tests)
           , (False, TestSuite.Queries.Int_Yices.tests)
           , (True,  TestSuite.Queries.Int_Z3.tests)
           , (True,  TestSuite.Queries.Interpolants.tests)
           , (True,  TestSuite.Queries.Uninterpreted.tests)
           , (True,  TestSuite.Uninterpreted.AUF.tests)
           , (True,  TestSuite.Uninterpreted.Axioms.tests)
           , (True,  TestSuite.Uninterpreted.Function.tests)
           , (True,  TestSuite.Uninterpreted.Sort.tests)
           , (True,  TestSuite.Uninterpreted.Uninterpreted.tests)
           ]
