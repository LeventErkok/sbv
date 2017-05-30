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
import qualified TestSuite.Basics.ArithNoSolver           as T02_01(testSuite)
import qualified TestSuite.Basics.BasicTests              as T02_03(testSuite)
import qualified TestSuite.BitPrecise.Legato              as T03_02(testSuite)
import qualified TestSuite.BitPrecise.MergeSort           as T03_03(testSuite)
import qualified TestSuite.CRC.CCITT                      as T04_01(testSuite)
import qualified TestSuite.CodeGeneration.AddSub          as T05_01(testSuite)
import qualified TestSuite.CodeGeneration.CgTests         as T05_02(testSuite)
import qualified TestSuite.CodeGeneration.CRC_USB5        as T05_03(testSuite)
import qualified TestSuite.CodeGeneration.Fibonacci       as T05_04(testSuite)
import qualified TestSuite.CodeGeneration.Floats          as T05_05(testSuite)
import qualified TestSuite.CodeGeneration.GCD             as T05_06(testSuite)
import qualified TestSuite.CodeGeneration.PopulationCount as T05_07(testSuite)
import qualified TestSuite.CodeGeneration.Uninterpreted   as T05_08(testSuite)
import qualified TestSuite.Crypto.AES                     as T06_01(testSuite)
import qualified TestSuite.Existentials.CRCPolynomial     as T07_01(testSuite)
import qualified TestSuite.Puzzles.Coins                  as T09_01(testSuite)
import qualified TestSuite.Puzzles.Counts                 as T09_02(testSuite)

-- Bool says whether we need a real SMT solver to run this test
-- Note that it's ok to say True even if an SMT solver is *not*
-- needed, but we'd like most things to be targeted False so that
-- those tests can be run as part of cabal.
allTestCases :: [(String, Bool, SBVTestSuite)]
allTestCases = [
       ("arithCF",     False, T02_01.testSuite)
     , ("basic",       False, T02_03.testSuite)
     , ("legato",      False, T03_02.testSuite)
     , ("mergeSort",   False, T03_03.testSuite)
     , ("ccitt",       False, T04_01.testSuite)
     , ("addSub",      False, T05_01.testSuite)
     , ("cgtest",      False, T05_02.testSuite)
     , ("cgUSB5",      False, T05_03.testSuite)
     , ("fib",         False, T05_04.testSuite)
     , ("floats",      False, T05_05.testSuite)
     , ("gcd",         False, T05_06.testSuite)
     , ("popCount",    False, T05_07.testSuite)
     , ("cgUninterp",  False, T05_08.testSuite)
     , ("aes",         False, T06_01.testSuite)
     , ("existPoly",   False, T07_01.testSuite)
     , ("coins",       False, T09_01.testSuite)
     , ("counts",      False, T09_02.testSuite)
     ]
