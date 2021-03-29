-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.PowerSet
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.Puzzles.PowerSet
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.PowerSet(tests) where

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Puzzles.PowerSet"
    [ testCase ("powerSet " ++ show i) (assert (pSet i)) | i <- [0 .. 7] ]

pSet :: Int -> IO Bool
pSet n = do cnt <- numberOfModels $ do mapM_ (\i -> sBool ('e' : show i)) [1..n]
                                       -- Look ma! No constraints!
                                       return sTrue
            return (cnt == 2^n)
