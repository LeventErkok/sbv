-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.TestSuite.Uninterpreted
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Uninterpreted.Uninterpreted
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.Uninterpreted(tests) where

import Examples.Uninterpreted.Uninterpreted
import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.Uninterpreted"
    [ testCase "uninterpreted-0" (assertIsThm p0)
    , testCase "uninterpreted-1" (assertIsThm p1)
    , testCase "uninterpreted-2" (assertIsntThm p2)
    ]
