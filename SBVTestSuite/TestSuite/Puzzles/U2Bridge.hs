-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.U2Bridge
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.U2Bridge
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.U2Bridge(tests) where

import Documentation.SBV.Examples.Puzzles.U2Bridge

import Data.List(sortOn)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Puzzles.U2Bridge"
    [ testCase "U2Bridge_cnt1" (assert $ (0 ==) `fmap` count 1)
    , testCase "U2Bridge_cnt2" (assert $ (0 ==) `fmap` count 2)
    , testCase "U2Bridge_cnt3" (assert $ (0 ==) `fmap` count 3)
    , testCase "U2Bridge_cnt4" (assert $ (0 ==) `fmap` count 4)
    , testCase "U2Bridge_cnt6" (assert $ (0 ==) `fmap` count 6)
    , goldenVsStringShow "U2Bridge" (slv 5)
    ]
 where act     = do b <- free_; p1 <- free_; p2 <- free_; return (b, p1, p2)
       count n = numberOfModels $ isValid `fmap` mapM (const act) [1..(n::Int)]
       slv n   = rearrange `fmap` allSat (isValid `fmap` mapM (const act) [1..(n::Int)])

       rearrange r@AllSatResult{allSatResults = ms} = r { allSatResults = sortOn (show . SatResult) ms }
