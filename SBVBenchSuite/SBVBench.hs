-----------------------------------------------------------------------------
-- |
-- Module    : SBVBench
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- We define this entry point to the benchsuite for use in fine-tuning SBV's
-- performance. It may be the case that a user wants to benchmark only one
-- particular feature or aspect of SBV and this entry point facilitates such a
-- "deep dive".
-----------------------------------------------------------------------------

module Main where

import           Gauge.Main.Options (defaultConfig, Config(..))

-- import           Utils.SBVBenchFramework

import Documentation.SBV.Examples.Puzzles.Counts

-- | Custom config to limit benchmarks to 5 minutes of runtime. This is required
-- because we can easily generate benchmarks that take a lot of wall time to
-- solve, especially with 'Data.SBV.allSatWith' calls
benchConfig :: Config
benchConfig = defaultConfig { timeLimit = Just 300.00 }

{-
This is the sister module to SBVBenchmark. Where SBVBenchmark provides the
continuous integration use case this module is reserved for deep dives into
particular aspects of SBV. One might use this entry point to only run a
particular benchmark of interest, or load and run a symbolic program to profile,
generate core code, or anything else. The workflow should be:

------------------------------
1. benchmark the code of interest
2. profile the code if you are looking for performance improvements
3. make your changes
4. repeat benchmark and profiling to confirm the effect of your changes
------------------------------

We recommend using a special file name, e.g., `filename <- benchResultsFile
"mergeableTuning"` to hold the benchmarks so that the before and after results
can be compared in the usual way with BenchShow: `cabal repl SBVBench;
compareBenchMarksCli "SBVBenchSuite/BenchFiles/mergeableTuning.csv"`
-}

main :: IO ()
main = do
  -- generate the benchmark file name
  -- let f = benchResultsFile "<your-test-name-here>"

  -- Your code on interest here
  putStrLn "running"
  counts

  -- satisfying the type system
  -- return ()
