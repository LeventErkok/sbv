-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Temperature
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Puzzles.Temperature
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Temperature(tests) where

import Data.SBV

import Examples.Puzzles.Temperature
import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Puzzles.Temperature"
    [ goldenVsStringShow "temperature" (allSat (revOf `fmap` exists_))
    ]
