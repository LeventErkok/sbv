-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Coins
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Puzzles.Coins
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Coins(testSuite) where

import Data.SBV
import Data.SBV.Examples.Puzzles.Coins

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "coins" ~: coinsPgm `goldCheck` "coins.gold"
 ]
 where coinsPgm = runSAT $ do cs <- mapM mkCoin [1..6]
                              mapM_ constrain [c s | s <- combinations cs, length s >= 2, c <- [c1, c2, c3, c4, c5, c6]]
                              constrain $ bAnd $ zipWith (.>=) cs (tail cs)
                              output $ sum cs .== 115
