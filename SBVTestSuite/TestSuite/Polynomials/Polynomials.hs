-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Polynomials.Polynomials
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Polynomials.Polynomials
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Polynomials.Polynomials(tests) where

import Documentation.SBV.Examples.Misc.Polynomials

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Polynomials.Polynomials"
    [ testCase "polynomial-1" (assertIsThm multUnit)
    , testCase "polynomial-2" (assertIsThm multComm)
    , testCase "polynomial-3" (assertIsThm polyDivMod)
    ]
