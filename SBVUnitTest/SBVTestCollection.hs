-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- SBV test collection
-----------------------------------------------------------------------------

module SBVTestCollection(allTestCases) where

import SBVTest

-- To add a new collection of tests, import below and add to allTestCases variable
import qualified TestSuite.Arrays.Memory                  as T01_01(testSuite)
import qualified TestSuite.Basics.ArithNoSolver           as T02_01(testSuite)
import qualified TestSuite.Basics.ArithSolver             as T02_02(testSuite)
import qualified TestSuite.Basics.BasicTests              as T02_03(testSuite)
import qualified TestSuite.Basics.Higher                  as T02_04(testSuite)
import qualified TestSuite.Basics.Index                   as T02_05(testSuite)
import qualified TestSuite.Basics.ProofTests              as T02_06(testSuite)
import qualified TestSuite.Basics.QRem                    as T02_07(testSuite)
import qualified TestSuite.BitPrecise.BitTricks           as T03_01(testSuite)
import qualified TestSuite.BitPrecise.Legato              as T03_02(testSuite)
import qualified TestSuite.BitPrecise.MergeSort           as T03_03(testSuite)
import qualified TestSuite.BitPrecise.PrefixSum           as T03_04(testSuite)
import qualified TestSuite.CRC.CCITT                      as T04_01(testSuite)
import qualified TestSuite.CRC.CCITT_Unidir               as T04_02(testSuite)
import qualified TestSuite.CRC.GenPoly                    as T04_03(testSuite)
import qualified TestSuite.CRC.Parity                     as T04_04(testSuite)
import qualified TestSuite.CRC.USB5                       as T04_05(testSuite)
import qualified TestSuite.CodeGeneration.AddSub          as T05_01(testSuite)
import qualified TestSuite.CodeGeneration.CgTests         as T05_02(testSuite)
import qualified TestSuite.CodeGeneration.CRC_USB5        as T05_03(testSuite)
import qualified TestSuite.CodeGeneration.Fibonacci       as T05_04(testSuite)
import qualified TestSuite.CodeGeneration.GCD             as T05_05(testSuite)
import qualified TestSuite.CodeGeneration.PopulationCount as T05_06(testSuite)
import qualified TestSuite.CodeGeneration.Uninterpreted   as T05_07(testSuite)
import qualified TestSuite.Crypto.AES                     as T06_01(testSuite)
import qualified TestSuite.Crypto.RC4                     as T06_02(testSuite)
import qualified TestSuite.Existentials.CRCPolynomial     as T07_01(testSuite)
import qualified TestSuite.Polynomials.Polynomials        as T08_01(testSuite)
import qualified TestSuite.Puzzles.Coins                  as T09_01(testSuite)
import qualified TestSuite.Puzzles.Counts                 as T09_02(testSuite)
import qualified TestSuite.Puzzles.DogCatMouse            as T09_03(testSuite)
import qualified TestSuite.Puzzles.Euler185               as T09_04(testSuite)
import qualified TestSuite.Puzzles.MagicSquare            as T09_05(testSuite)
import qualified TestSuite.Puzzles.NQueens                as T09_06(testSuite)
import qualified TestSuite.Puzzles.PowerSet               as T09_07(testSuite)
import qualified TestSuite.Puzzles.Sudoku                 as T09_08(testSuite)
import qualified TestSuite.Puzzles.Temperature            as T09_09(testSuite)
import qualified TestSuite.Puzzles.U2Bridge               as T09_10(testSuite)
import qualified TestSuite.Uninterpreted.AUF              as T10_01(testSuite)
import qualified TestSuite.Uninterpreted.Function         as T10_02(testSuite)
import qualified TestSuite.Uninterpreted.Uninterpreted    as T10_03(testSuite)

-- Bool says whether we need a real SMT solver to run this test
-- Note that it's ok to say True even if an SMT solver is *not*
-- needed, but we'd like most things to be targeted False so that
-- those tests can be run as part of cabal.
allTestCases :: [(String, Bool, SBVTestSuite)]
allTestCases = [
       ("mem",         True,  T01_01.testSuite)
     , ("arithCF",     False, T02_01.testSuite)
     , ("arith",       True,  T02_02.testSuite)
     , ("basic",       False, T02_03.testSuite)
     , ("higher",      True,  T02_04.testSuite)
     , ("index",       True,  T02_05.testSuite)
     , ("proof",       True,  T02_06.testSuite)
     , ("qrem",        True,  T02_07.testSuite)
     , ("bitTricks",   True,  T03_01.testSuite)
     , ("legato",      False, T03_02.testSuite)
     , ("mergeSort",   False, T03_03.testSuite)
     , ("prefixSum",   True,  T03_04.testSuite)
     , ("ccitt",       False, T04_01.testSuite)
     , ("ccitt2",      True,  T04_02.testSuite)
     , ("genPoly",     True,  T04_03.testSuite)
     , ("parity",      True,  T04_04.testSuite)
     , ("usb5",        True,  T04_05.testSuite)
     , ("addSub",      False, T05_01.testSuite)
     , ("cgtest",      False, T05_02.testSuite)
     , ("cgUSB5",      False, T05_03.testSuite)
     , ("fib",         False, T05_04.testSuite)
     , ("gcd",         False, T05_05.testSuite)
     , ("popCount",    False, T05_06.testSuite)
     , ("cgUninterp",  False, T05_07.testSuite)
     , ("aes",         False, T06_01.testSuite)
     , ("rc4",         True,  T06_02.testSuite)
     , ("existPoly",   False, T07_01.testSuite)
     , ("poly",        True,  T08_01.testSuite)
     , ("coins",       False, T09_01.testSuite)
     , ("counts",      False, T09_02.testSuite)
     , ("dogCatMouse", True,  T09_03.testSuite)
     , ("euler185",    True,  T09_04.testSuite)
     , ("magicSquare", True,  T09_05.testSuite)
     , ("nQueens",     True,  T09_06.testSuite)
     , ("powerset",    True,  T09_07.testSuite)
     , ("sudoku",      True,  T09_08.testSuite)
     , ("temperature", True,  T09_09.testSuite)
     , ("u2bridge",    True,  T09_10.testSuite)
     , ("auf1",        True,  T10_01.testSuite)
     , ("auf2",        True,  T10_02.testSuite)
     , ("unint",       True,  T10_03.testSuite)
     ]
