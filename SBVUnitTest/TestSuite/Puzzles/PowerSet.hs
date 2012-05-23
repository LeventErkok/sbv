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

module TestSuite.Puzzles.PowerSet(testSuite) where

import Data.SBV

import Examples.Puzzles.PowerSet
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [ "powerSet " ++ show i ~: assert (pSet i) | i <- [0 .. 7] ]
 where pSet :: Int -> IO Bool
       pSet n = do cnt <- numberOfModels $ genPowerSet `fmap` mkExistVars n
                   return (cnt == 2^n)
