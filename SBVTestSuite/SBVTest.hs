-----------------------------------------------------------------------------
-- |
-- Module    : SBVTest
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Main entry point to the test suite
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Main(main) where

import Test.Tasty

import qualified TestSuite.Arrays.InitVals
import qualified TestSuite.Arrays.Memory
import qualified TestSuite.Arrays.Query
import qualified TestSuite.Arrays.Caching
import qualified TestSuite.Basics.AllSat
import qualified TestSuite.Basics.ArbFloats
import qualified TestSuite.Basics.ArithNoSolver
import qualified TestSuite.Basics.ArithSolver
import qualified TestSuite.Basics.Assert
import qualified TestSuite.Basics.BasicTests
import qualified TestSuite.Basics.BarrelRotate
import qualified TestSuite.Basics.BoundedList
import qualified TestSuite.Basics.DynSign
import qualified TestSuite.Basics.Exceptions
import qualified TestSuite.Basics.EqSym
import qualified TestSuite.Basics.GenBenchmark
import qualified TestSuite.Basics.Higher
import qualified TestSuite.Basics.Index
import qualified TestSuite.Basics.IteTest
import qualified TestSuite.Basics.Lambda
import qualified TestSuite.Basics.List
import qualified TestSuite.Basics.ModelValidate
import qualified TestSuite.Basics.Nonlinear
import qualified TestSuite.Basics.ProofTests
import qualified TestSuite.Basics.PseudoBoolean
import qualified TestSuite.Basics.QRem
import qualified TestSuite.Basics.Quantifiers
import qualified TestSuite.Basics.Recursive
import qualified TestSuite.Basics.Set
import qualified TestSuite.Basics.SmallShifts
import qualified TestSuite.Basics.SquashReals
import qualified TestSuite.Basics.String
import qualified TestSuite.Basics.Sum
import qualified TestSuite.Basics.TOut
import qualified TestSuite.Basics.Tuple
import qualified TestSuite.Basics.UISat
import qualified TestSuite.BitPrecise.BitTricks
import qualified TestSuite.BitPrecise.Legato
import qualified TestSuite.BitPrecise.MergeSort
import qualified TestSuite.BitPrecise.PrefixSum
import qualified TestSuite.CantTypeCheck.Misc
import qualified TestSuite.Char.Char
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
import qualified TestSuite.Crypto.SHA
import qualified TestSuite.GenTest.GenTests
import qualified TestSuite.Optimization.AssertWithPenalty
import qualified TestSuite.Optimization.Basics
import qualified TestSuite.Optimization.Combined
import qualified TestSuite.Optimization.ExtensionField
import qualified TestSuite.Optimization.Floats
import qualified TestSuite.Optimization.NoOpt
import qualified TestSuite.Optimization.Quantified
import qualified TestSuite.Optimization.Reals
import qualified TestSuite.Optimization.Tuples
import qualified TestSuite.Overflows.Arithmetic
import qualified TestSuite.Overflows.Casts
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
import qualified TestSuite.Queries.ArrayGetVal
import qualified TestSuite.Queries.BasicQuery
import qualified TestSuite.Queries.BadOption
import qualified TestSuite.Queries.DSat
import qualified TestSuite.Queries.Enums
import qualified TestSuite.Queries.FreshVars
import qualified TestSuite.Queries.Int_ABC
import qualified TestSuite.Queries.Int_Boolector
import qualified TestSuite.Queries.Int_CVC4
import qualified TestSuite.Queries.Int_Mathsat
import qualified TestSuite.Queries.Int_Yices
import qualified TestSuite.Queries.Int_Z3
import qualified TestSuite.Queries.Interpolants
import qualified TestSuite.Queries.Lists
import qualified TestSuite.Queries.Strings
import qualified TestSuite.Queries.Sums
import qualified TestSuite.Queries.Tables
import qualified TestSuite.Queries.Tuples
import qualified TestSuite.Queries.UISat
import qualified TestSuite.Queries.UISatEx
import qualified TestSuite.Queries.Uninterpreted
import qualified TestSuite.QuickCheck.QC
import qualified TestSuite.Transformers.SymbolicEval
import qualified TestSuite.Uninterpreted.AUF
import qualified TestSuite.Uninterpreted.Axioms
import qualified TestSuite.Uninterpreted.Function
import qualified TestSuite.Uninterpreted.Sort
import qualified TestSuite.Uninterpreted.Uninterpreted

main :: IO ()
main = defaultMain $ testGroup "SBV" [
                        TestSuite.Arrays.InitVals.tests
                      , TestSuite.Arrays.Memory.tests
                      , TestSuite.Arrays.Query.tests
                      , TestSuite.Arrays.Caching.tests
                      , TestSuite.Basics.AllSat.tests
                      , TestSuite.Basics.ArbFloats.tests
                      , TestSuite.Basics.ArithNoSolver.tests
                      , TestSuite.Basics.ArithSolver.tests
                      , TestSuite.Basics.Assert.tests
                      , TestSuite.Basics.BarrelRotate.tests
                      , TestSuite.Basics.BasicTests.tests
                      , TestSuite.Basics.BoundedList.tests
                      , TestSuite.Basics.DynSign.tests
                      , TestSuite.Basics.EqSym.tests
                      , TestSuite.Basics.Exceptions.testsLocal
                      , TestSuite.Basics.Exceptions.testsRemote
                      , TestSuite.Basics.GenBenchmark.tests
                      , TestSuite.Basics.Higher.tests
                      , TestSuite.Basics.Index.tests
                      , TestSuite.Basics.IteTest.tests
                      , TestSuite.Basics.Lambda.tests
                      , TestSuite.Basics.List.tests
                      , TestSuite.Basics.ModelValidate.tests
                      , TestSuite.Basics.ModelValidate.testsABC
                      , TestSuite.Basics.Nonlinear.tests
                      , TestSuite.Basics.ProofTests.tests
                      , TestSuite.Basics.PseudoBoolean.tests
                      , TestSuite.Basics.QRem.tests
                      , TestSuite.Basics.Quantifiers.tests
                      , TestSuite.Basics.Recursive.tests
                      , TestSuite.Basics.Set.tests
                      , TestSuite.Basics.SmallShifts.tests
                      , TestSuite.Basics.SquashReals.tests
                      , TestSuite.Basics.String.tests
                      , TestSuite.Basics.Sum.tests
                      , TestSuite.Basics.TOut.tests
                      , TestSuite.Basics.Tuple.tests
                      , TestSuite.Basics.UISat.tests
                      , TestSuite.BitPrecise.BitTricks.tests
                      , TestSuite.BitPrecise.Legato.tests
                      , TestSuite.BitPrecise.MergeSort.tests
                      , TestSuite.BitPrecise.PrefixSum.tests
                      , TestSuite.CantTypeCheck.Misc.tests
                      , TestSuite.Char.Char.tests
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
                      , TestSuite.Crypto.SHA.tests
                      , TestSuite.GenTest.GenTests.tests
                      , TestSuite.Optimization.AssertWithPenalty.tests
                      , TestSuite.Optimization.Basics.tests
                      , TestSuite.Optimization.Combined.tests
                      , TestSuite.Optimization.ExtensionField.tests
                      , TestSuite.Optimization.Floats.tests
                      , TestSuite.Optimization.NoOpt.tests
                      , TestSuite.Optimization.Tuples.tests
                      , TestSuite.Optimization.Quantified.tests
                      , TestSuite.Optimization.Reals.tests
                      , TestSuite.Overflows.Arithmetic.tests
                      , TestSuite.Overflows.Casts.tests
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
                      , TestSuite.Queries.BadOption.tests
                      , TestSuite.Queries.ArrayGetVal.tests
                      , TestSuite.Queries.BasicQuery.tests
                      , TestSuite.Queries.DSat.tests
                      , TestSuite.Queries.Interpolants.tests
                      , TestSuite.Queries.Enums.tests
                      , TestSuite.Queries.FreshVars.tests
                      , TestSuite.Queries.Int_Z3.tests
                      , TestSuite.Queries.Int_ABC.tests
                      , TestSuite.Queries.Int_Boolector.tests
                      , TestSuite.Queries.Int_CVC4.tests
                      , TestSuite.Queries.Int_Mathsat.tests
                      , TestSuite.Queries.Int_Yices.tests
                      , TestSuite.Queries.Lists.tests
                      , TestSuite.Queries.Strings.tests
                      , TestSuite.Queries.Sums.tests
                      , TestSuite.Queries.Tables.tests
                      , TestSuite.Queries.Tuples.tests
                      , TestSuite.Queries.UISat.tests
                      , TestSuite.Queries.UISatEx.tests
                      , TestSuite.Queries.Uninterpreted.tests
                      , TestSuite.QuickCheck.QC.tests
                      , TestSuite.Transformers.SymbolicEval.tests
                      , TestSuite.Uninterpreted.AUF.tests
                      , TestSuite.Uninterpreted.Axioms.tests
                      , TestSuite.Uninterpreted.Function.tests
                      , TestSuite.Uninterpreted.Sort.tests
                      , TestSuite.Uninterpreted.Uninterpreted.tests
                      ]
