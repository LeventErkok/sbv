-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Puzzles.PowerSet
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.PowerSet
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Puzzles.PowerSet(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.PowerSet

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [ "powerSet " ++ show i ~: assert (pSet i) | i <- [0 .. 7] ]
 where pSet :: Int -> IO Bool
       pSet n = do cnt <- numberOfModels $ genPowerSet `fmap` mkExistVars n
                   return (cnt == 2^n)
