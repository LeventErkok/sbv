-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.Coins
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.Coins
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.Coins(tests) where

import Documentation.SBV.Examples.Puzzles.Coins

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Puzzles.Coins" [
  goldenVsStringShow "coins" coinsPgm
 ]
 where coinsPgm = runSAT $ do cs <- mapM mkCoin [1..6]
                              mapM_ constrain [c s | s <- combinations cs, length s >= 2, c <- [c1, c2, c3, c4, c5, c6]]
                              constrain $ sAnd $ zipWith (.>=) cs (drop 1 cs)
                              pure $ sum cs .== 115
