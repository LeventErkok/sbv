-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Uninterpreted.AUF
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Uninterpreted.AUF where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Uninterpreted.AUF

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "auf-0" ~: assert =<< isTheorem thm1
 , "auf-1" ~: assert =<< isTheorem thm2
 , "auf-2" ~: pgm `goldCheck` "auf-1.gold"
 ]
 where pgm = runSymbolic $ forAll ["x", "y", "a", "initVal"] thm1
