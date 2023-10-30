-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.GenBenchmark
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the generateSMTBenchmark function.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.GenBenchmark(tests)  where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.genBenchmark"
    [ goldenString "genBenchMark1" $ gen generateSMTBenchmarkProof (\x -> x .== (x+1::SWord8))
    , goldenString "genBenchMark2" $ gen generateSMTBenchmarkSat   (\x -> x .== (x+1::SWord8))
    ]
    where gen generator f =
                -- the first line is time-stamp, get rid of it so test is repeatable
                unlines . drop 1 . lines <$> generator f
