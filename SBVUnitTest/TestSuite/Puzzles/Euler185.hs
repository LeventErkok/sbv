-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Euler185
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Puzzles.Euler185
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Euler185(tests) where

import Data.SBV
import Data.SBV.Examples.Puzzles.Euler185

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Puzzles.Euler185"
    [ goldenVsStringShow "euler185" "euler185.gold" (allSat euler185)
    ]
