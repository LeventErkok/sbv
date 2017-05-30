-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.U2Bridge
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Puzzles.U2Bridge
-----------------------------------------------------------------------------

module TestSuite.Puzzles.U2Bridge(tests) where

import Data.SBV
import Data.SBV.Examples.Puzzles.U2Bridge

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Puzzles.U2Bridge"
    [ testCase "U2Bridge-1" (assert $ (0 ==) `fmap` count 1)
    , testCase "U2Bridge-2" (assert $ (0 ==) `fmap` count 2)
    , testCase "U2Bridge-3" (assert $ (0 ==) `fmap` count 3)
    , testCase "U2Bridge-4" (assert $ (0 ==) `fmap` count 4)
    , goldenVsStringShow "U2Bridge-5" "U2Bridge.gold" (slv 5)
    , testCase "U2Bridge-6" (assert $ (0 ==) `fmap` count 6)
    ]
 where act     = do b <- exists_; p1 <- exists_; p2 <- exists_; return (b, p1, p2)
       count n = numberOfModels $ isValid `fmap` mapM (const act) [1..(n::Int)]
       slv n   = sat $ isValid `fmap` mapM (const act) [1..(n::Int)]
