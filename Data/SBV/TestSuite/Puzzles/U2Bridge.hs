-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Puzzles.U2Bridge
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.U2Bridge
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Puzzles.U2Bridge(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.U2Bridge

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "U2Bridge-1" ~: assert $ (0 ==) `fmap` count 1
 , "U2Bridge-2" ~: assert $ (0 ==) `fmap` count 2
 , "U2Bridge-3" ~: assert $ (0 ==) `fmap` count 3
 , "U2Bridge-4" ~: assert $ (0 ==) `fmap` count 4
 , "U2Bridge-5" ~: solve 5 `goldCheck` "U2Bridge.gold"
 , "U2Bridge-6" ~: assert $ (0 ==) `fmap` count 6
 ]
 where act     = do b <- free_; p1 <- free_; p2 <- free_; return (b, p1, p2)
       count n = numberOfModels $ mapM (const act) [1..(n::Int)] >>= output . isValid
       solve n = sat $ mapM (const act) [1..(n::Int)] >>= output . isValid
