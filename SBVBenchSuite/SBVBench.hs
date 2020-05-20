-----------------------------------------------------------------------------
-- |
-- Module    : SBVBench
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Main entry point to the bench suite.
-----------------------------------------------------------------------------

module Main where

import           Gauge.Main
import           Gauge.Main.Options (defaultConfig, Config(..))

import           Utils.SBVBenchFramework

import           BenchSuite.Bench.Bench

-- | Puzzles
import qualified BenchSuite.Puzzles.Birthday
import qualified BenchSuite.Puzzles.Coins
import qualified BenchSuite.Puzzles.Counts
import qualified BenchSuite.Puzzles.DogCatMouse
import qualified BenchSuite.Puzzles.Euler185
import qualified BenchSuite.Puzzles.Garden
import qualified BenchSuite.Puzzles.LadyAndTigers
import qualified BenchSuite.Puzzles.MagicSquare
import qualified BenchSuite.Puzzles.NQueens
import qualified BenchSuite.Puzzles.SendMoreMoney
import qualified BenchSuite.Puzzles.Sudoku
import qualified BenchSuite.Puzzles.U2Bridge

-- | BitPrecise
import qualified BenchSuite.BitPrecise.BitTricks
import qualified BenchSuite.BitPrecise.BrokenSearch
import qualified BenchSuite.BitPrecise.Legato
import qualified BenchSuite.BitPrecise.MergeSort
import qualified BenchSuite.BitPrecise.MultMask
import qualified BenchSuite.BitPrecise.PrefixSum

-- | Queries
import qualified BenchSuite.Queries.AllSat
import qualified BenchSuite.Queries.CaseSplit
import qualified BenchSuite.Queries.Concurrency
import qualified BenchSuite.Queries.Enums
import qualified BenchSuite.Queries.FourFours
import qualified BenchSuite.Queries.GuessNumber
import qualified BenchSuite.Queries.Interpolants
import qualified BenchSuite.Queries.UnsatCore

-- | Custom config to limit benchmarks to 5 minutes of runtime. This is required
-- because we can easily generate benchmarks that take a lot of wall time to
-- solve, especially with 'Data.SBV.allSatWith' calls
benchConfig :: Config
benchConfig = defaultConfig {timeLimit = Just 300.00}

-- The bench harness
main :: IO ()
main = defaultMainWith benchConfig $
       [ puzzles
       , bitPrecise
       , queries
       ]

-- | Benchmarks for 'Documentation.SBV.Examples.Puzzles'. Each benchmark file
-- defines a 'benchmarks' function which returns a
-- 'BenchSuite.Bench.Bench.Runner'. We want to allow benchmarks to be defined as
-- closely as possible to the problems being solved. But for practical reasons
-- we may desire to prevent benchmarking 'Data.SBV.allSat' calls because they
-- could timeout. Thus by using 'BenchSuite.Bench.Bench.Runner' we can define
-- the benchmark mirroring the logic of the symbolic program and change solver
-- details _without_ redefining the benchmark, as I have done below by
-- converting all examples to use 'Data.SBV.satWith'. For benchmarks which do
-- not need to run with different solver configurations, such as queries we run
-- with `BenchSuite.Bench.Bench.Runner.runIO`
puzzles :: Benchmark
puzzles = bgroup "Puzzles" $ runBenchMark <$>
          [ BenchSuite.Puzzles.Coins.benchmarks
          , BenchSuite.Puzzles.Counts.benchmarks
          , BenchSuite.Puzzles.Birthday.benchmarks
          , BenchSuite.Puzzles.DogCatMouse.benchmarks
          , BenchSuite.Puzzles.Euler185.benchmarks
          , BenchSuite.Puzzles.Garden.benchmarks
          , BenchSuite.Puzzles.LadyAndTigers.benchmarks
          , BenchSuite.Puzzles.SendMoreMoney.benchmarks
          , BenchSuite.Puzzles.NQueens.benchmarks
          , BenchSuite.Puzzles.MagicSquare.benchmarks
          , BenchSuite.Puzzles.Sudoku.benchmarks
          , BenchSuite.Puzzles.U2Bridge.benchmarks
          ]

bitPrecise :: Benchmark
bitPrecise = bgroup "BitPrecise" $ runBenchMark <$>
             [ BenchSuite.BitPrecise.BitTricks.benchmarks
             , BenchSuite.BitPrecise.BrokenSearch.benchmarks
             , BenchSuite.BitPrecise.Legato.benchmarks
             , BenchSuite.BitPrecise.MergeSort.benchmarks
             , BenchSuite.BitPrecise.MultMask.benchmarks
             , BenchSuite.BitPrecise.PrefixSum.benchmarks
             ]

queries :: Benchmark
queries = bgroup "Queries" $ runBenchMark <$>
          [ BenchSuite.Queries.AllSat.benchmarks
          , BenchSuite.Queries.CaseSplit.benchmarks
          , BenchSuite.Queries.Concurrency.benchmarks
          , BenchSuite.Queries.Enums.benchmarks
          , BenchSuite.Queries.FourFours.benchmarks
          , BenchSuite.Queries.GuessNumber.benchmarks
          , BenchSuite.Queries.Interpolants.benchmarks
          , BenchSuite.Queries.UnsatCore.benchmarks
          ]
