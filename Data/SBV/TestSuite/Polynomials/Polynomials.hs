-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Polynomials.Polynomials
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Polynomials.Polynomials
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Polynomials.Polynomials(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Polynomials.Polynomials

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "polynomial-1" ~: assert =<< isTheorem multUnit
 , "polynomial-2" ~: assert =<< isTheorem multComm
 , "polynomial-3" ~: assert =<< isTheorem polyDivMod
 ]
