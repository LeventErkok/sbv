-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Polynomials.Polynomials
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Polynomials.Polynomials
-----------------------------------------------------------------------------

module TestSuite.Polynomials.Polynomials(testSuite) where

import Data.SBV.Examples.Polynomials.Polynomials

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "polynomial-1" ~: assert =<< isThm multUnit
 , "polynomial-2" ~: assert =<< isThm multComm
 , "polynomial-3" ~: assert =<< isThm polyDivMod
 ]
