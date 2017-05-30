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

module TestSuite.Polynomials.Polynomials(tests) where

import Data.SBV.Examples.Polynomials.Polynomials

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Polynomials.Polynomials"
    [ testCase "polynomial-1" (assertIsThm multUnit)
    , testCase "polynomial-2" (assertIsThm multComm)
    , testCase "polynomial-3" (assertIsThm polyDivMod)
    ]
