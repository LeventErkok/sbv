-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.GenBenchmark
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the generateSMTBenchmark function.
-----------------------------------------------------------------------------

module TestSuite.Basics.GenBenchmark(tests)  where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.genBenchmark"
    [ goldenString "genBenchMark1" $ gen False (\x -> x .== (x+1::SWord8))
    , goldenString "genBenchMark2" $ gen True  (\x -> x .== (x+1::SWord8))
    ]
    where gen b f = -- the first line is time-stamp, get rid of it so test is repeatable
                    unlines . tail . lines <$> generateSMTBenchmark b f
