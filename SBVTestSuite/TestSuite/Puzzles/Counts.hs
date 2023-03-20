-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.Counts
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.Counts
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.Counts(tests) where

import Documentation.SBV.Examples.Puzzles.Counts

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Puzzles.Counts" [
  goldenVsStringShow "counts" countPgm
 ]
 where countPgm = runSAT $ puzzle <$> mkFreeVars 10
