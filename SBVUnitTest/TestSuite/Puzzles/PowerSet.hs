-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.PowerSet
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Puzzles.PowerSet
-----------------------------------------------------------------------------

module TestSuite.Puzzles.PowerSet(tests) where

import Data.SBV

import Examples.Puzzles.PowerSet
import SBVTest

tests :: TestTree
tests =
  testGroup "Puzzles.PowerSet"
    [ testCase ("powerSet " ++ show i) (assert (pSet i)) | i <- [0 .. 7] ]

pSet :: Int -> IO Bool
pSet n = do cnt <- numberOfModels $ genPowerSet `fmap` mkExistVars n
            return (cnt == 2^n)
