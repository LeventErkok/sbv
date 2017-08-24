{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Test.Tasty

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..), CIOS(..), pickTests)

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
import qualified TestSuite.Basics.SmallShifts
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
import qualified TestSuite.Optimization.Quantified
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

-- On remote machines for Appveyor/Travis, the build machines doesn't have enough memory
-- and/or powerful enough to run our heavy tests; so we skip tests for Windows hosts and
-- reduce them for OSX. For Linux, we run them all. Note that this is only for remote
-- hosts; when we run locally, all tests are run.
--
-- TODO: Would be nice to run them all on Windows/OSX on remote hosts as well.
ciFilter :: CIOS -> Int -> TestTree -> IO TestTree
ciFilter _  100 tt = return tt
ciFilter os   n tt = do putStrLn $ "OS: " ++ show os ++ ", Running only " ++ show n ++ "% of tests."
                        pickTests n tt

main :: IO ()
main = do (testEnv, testPercentage) <- getTestEnvironment

          putStrLn $ "SBVTest: Test platform: " ++ show testEnv

          case testEnv of
            TestEnvUnknown   -> do putStrLn "Unknown test environment, skipping tests"
                                   exitSuccess

            TestEnvLocal     -> defaultMain $ testGroup "Local" [heavyTests, localOnlyTests, otherTests]

            TestEnvCI os     -> do reducedHeavyTests <- ciFilter os testPercentage heavyTests
                                   defaultMain $ testGroup "Remote" [reducedHeavyTests, otherTests]

-- | The following tests take too long/too burdensome for remote tests, so we run only a percentage of them
heavyTests :: TestTree
heavyTests = testGroup "SBVHeavyTests" [TestSuite.Basics.ArithSolver.tests]

-- | The following tests can only be run locally
localOnlyTests :: TestTree
localOnlyTests = testGroup "SBVLocalOnlyTests" [
                     TestSuite.Queries.BasicQuery.tests
                   , TestSuite.Queries.BadOption.tests
                   , TestSuite.Queries.Int_ABC.tests
                   , TestSuite.Queries.Int_Boolector.tests
                   , TestSuite.Queries.Int_CVC4.tests
                   , TestSuite.Queries.Int_Mathsat.tests
                   , TestSuite.Queries.Int_Yices.tests
                   ]

-- | Remaining tests
otherTests :: TestTree
otherTests = testGroup "SBVOtherTests" [
                 TestSuite.Arrays.Memory.tests
               , TestSuite.Basics.AllSat.tests
               , TestSuite.Basics.ArithNoSolver.tests
               , TestSuite.Basics.BasicTests.tests
               , TestSuite.Basics.GenBenchmark.tests
               , TestSuite.Basics.Higher.tests
               , TestSuite.Basics.Index.tests
               , TestSuite.Basics.IteTest.tests
               , TestSuite.Basics.ProofTests.tests
               , TestSuite.Basics.PseudoBoolean.tests
               , TestSuite.Basics.QRem.tests
               , TestSuite.Basics.Quantifiers.tests
               , TestSuite.Basics.Recursive.tests
               , TestSuite.Basics.SmallShifts.tests
               , TestSuite.Basics.SquashReals.tests
               , TestSuite.Basics.TOut.tests
               , TestSuite.BitPrecise.BitTricks.tests
               , TestSuite.BitPrecise.Legato.tests
               , TestSuite.BitPrecise.MergeSort.tests
               , TestSuite.BitPrecise.PrefixSum.tests
               , TestSuite.CodeGeneration.AddSub.tests
               , TestSuite.CodeGeneration.CgTests.tests
               , TestSuite.CodeGeneration.CRC_USB5.tests
               , TestSuite.CodeGeneration.Fibonacci.tests
               , TestSuite.CodeGeneration.Floats.tests
               , TestSuite.CodeGeneration.GCD.tests
               , TestSuite.CodeGeneration.PopulationCount.tests
               , TestSuite.CodeGeneration.Uninterpreted.tests
               , TestSuite.CRC.CCITT.tests
               , TestSuite.CRC.CCITT_Unidir.tests
               , TestSuite.CRC.GenPoly.tests
               , TestSuite.CRC.Parity.tests
               , TestSuite.CRC.USB5.tests
               , TestSuite.Crypto.AES.tests
               , TestSuite.Crypto.RC4.tests
               , TestSuite.Existentials.CRCPolynomial.tests
               , TestSuite.GenTest.GenTests.tests
               , TestSuite.Optimization.AssertSoft.tests
               , TestSuite.Optimization.Basics.tests
               , TestSuite.Optimization.Combined.tests
               , TestSuite.Optimization.ExtensionField.tests
               , TestSuite.Optimization.Quantified.tests
               , TestSuite.Optimization.Reals.tests
               , TestSuite.Polynomials.Polynomials.tests
               , TestSuite.Puzzles.Coins.tests
               , TestSuite.Puzzles.Counts.tests
               , TestSuite.Puzzles.DogCatMouse.tests
               , TestSuite.Puzzles.Euler185.tests
               , TestSuite.Puzzles.MagicSquare.tests
               , TestSuite.Puzzles.NQueens.tests
               , TestSuite.Puzzles.PowerSet.tests
               , TestSuite.Puzzles.Sudoku.tests
               , TestSuite.Puzzles.Temperature.tests
               , TestSuite.Puzzles.U2Bridge.tests
               , TestSuite.Queries.Enums.tests
               , TestSuite.Queries.FreshVars.tests
               , TestSuite.Queries.Int_Z3.tests
               , TestSuite.Queries.Interpolants.tests
               , TestSuite.Queries.Uninterpreted.tests
               , TestSuite.Uninterpreted.AUF.tests
               , TestSuite.Uninterpreted.Axioms.tests
               , TestSuite.Uninterpreted.Function.tests
               , TestSuite.Uninterpreted.Sort.tests
               , TestSuite.Uninterpreted.Uninterpreted.tests
               ]
