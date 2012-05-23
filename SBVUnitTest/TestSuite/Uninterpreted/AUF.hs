-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.AUF
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.AUF where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Uninterpreted.AUF

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "auf-0" ~: assert =<< isTheorem thm1
 , "auf-1" ~: assert =<< isTheorem thm2
 , "auf-2" ~: pgm `goldCheck` "auf-1.gold"
 ]
 where pgm = runSymbolic True $ forAll ["x", "y", "a", "initVal"] thm1 >>= output
