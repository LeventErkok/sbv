-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.NQueens
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.NQueens
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.NQueens(tests) where

import Documentation.SBV.Examples.Puzzles.NQueens

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Puzzles.NQueens"
    -- number of *distinct* solutions is given in http://en.wikipedia.org/wiki/Eight_queens_puzzle
   [ testCase "nQueens 1" (assert $ (==  1) `fmap` numberOfModels (mkQueens 1))
   , testCase "nQueens 2" (assert $ (==  0) `fmap` numberOfModels (mkQueens 2))
   , testCase "nQueens 3" (assert $ (==  0) `fmap` numberOfModels (mkQueens 3))
   , testCase "nQueens 4" (assert $ (==  2) `fmap` numberOfModels (mkQueens 4))
   , testCase "nQueens 5" (assert $ (== 10) `fmap` numberOfModels (mkQueens 5))
   , testCase "nQueens 6" (assert $ (==  4) `fmap` numberOfModels (mkQueens 6))
   , testCase "nQueens 7" (assert $ (== 40) `fmap` numberOfModels (mkQueens 7))
   , testCase "nQueens 8" (assert $ (== 92) `fmap` numberOfModels (mkQueens 8))
   ]

mkQueens :: Int -> Symbolic SBool
mkQueens n = isValid n `fmap` mkFreeVars n
