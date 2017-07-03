-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.Function
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testsuite for Data.SBV.Examples.Uninterpreted.Function
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.Function(tests) where

import Data.SBV.Examples.Uninterpreted.Function

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Uninterpreted.Function"
  [ testCase "aufunc-0" (assertIsThm thmGood)
  ]
