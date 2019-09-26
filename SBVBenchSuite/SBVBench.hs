-----------------------------------------------------------------------------
-- |
-- Module    : SBVBench
-- Copyright : (c) Jeffrey Young
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Main entry point to the bench suite.
-----------------------------------------------------------------------------

module Main where

import           Criterion.Main
import           Criterion.Types                  (Config (..))

import           Utils.SBVBenchFramework

import           BenchSuite.Overhead.SBVOverhead

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

-- | Custom config to limit benchmarks to 5 minutes of runtime. This is required
-- because we can easily generate benchmarks that take a lot of wall time to
-- solve, especially with 'Data.SBV.allSatWith' calls
benchConfig :: Config
benchConfig = defaultConfig {timeLimit = 300.00}

-- The bench harness
main :: IO ()
main = defaultMainWith benchConfig $
       [ puzzles
       ]

-- | Benchmarks for 'Documentation.SBV.Examples.Puzzles'. Each benchmark file
-- defines a 'benchmarks' function which returns a
-- 'BenchSuite.Overhead.SBVOverhead.Runner'. We want to allow benchmarks to be
-- defined as closely as possible to the problems being solver. But for
-- practical reasons we may desire to prevent benchmarking 'Data.SBV.allSat'
-- calls because they could timeout. Thus by using
-- 'BenchSuite.Overhead.SBVOverhead.Runner' we can define the benchmark
-- mirroring the logic of the symbolic program. But that might be expensive to
-- benchmark, so using this method we can change solver details _without_
-- redefining the benchmark, as I have done below by converting all examples to
-- use 'Data.SBV.satWith'.
puzzles :: Benchmark
puzzles = bgroup "Puzzles" $ (mkOverheadBenchMark . setRunner satWith) <$>
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
