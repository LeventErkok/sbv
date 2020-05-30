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

-- | Weakest Preconditions
import qualified BenchSuite.WeakestPreconditions.Append
import qualified BenchSuite.WeakestPreconditions.Basics
import qualified BenchSuite.WeakestPreconditions.Fib
import qualified BenchSuite.WeakestPreconditions.GCD
import qualified BenchSuite.WeakestPreconditions.IntDiv
import qualified BenchSuite.WeakestPreconditions.IntSqrt
import qualified BenchSuite.WeakestPreconditions.Length
import qualified BenchSuite.WeakestPreconditions.Sum

-- | Optimization
import qualified BenchSuite.Optimization.Enumerate
import qualified BenchSuite.Optimization.ExtField
import qualified BenchSuite.Optimization.LinearOpt
import qualified BenchSuite.Optimization.Production
import qualified BenchSuite.Optimization.VM

-- | Uninterpreted
import qualified BenchSuite.Uninterpreted.AUF
import qualified BenchSuite.Uninterpreted.Deduce
import qualified BenchSuite.Uninterpreted.Function
import qualified BenchSuite.Uninterpreted.Multiply
import qualified BenchSuite.Uninterpreted.Shannon
import qualified BenchSuite.Uninterpreted.Sort
import qualified BenchSuite.Uninterpreted.UISortAllSat

-- | Proof Tools
import qualified BenchSuite.ProofTools.BMC
import qualified BenchSuite.ProofTools.Fibonacci
import qualified BenchSuite.ProofTools.Strengthen
import qualified BenchSuite.ProofTools.Sum

-- | Code Generation
import qualified BenchSuite.CodeGeneration.AddSub
import qualified BenchSuite.CodeGeneration.CRC_USB5
import qualified BenchSuite.CodeGeneration.Fibonacci
import qualified BenchSuite.CodeGeneration.GCD
import qualified BenchSuite.CodeGeneration.PopulationCount
import qualified BenchSuite.CodeGeneration.Uninterpreted

-- | Crypto
import qualified BenchSuite.Crypto.AES
import qualified BenchSuite.Crypto.RC4
import qualified BenchSuite.Crypto.SHA

-- | Miscellaneous
import qualified BenchSuite.Misc.Auxiliary
import qualified BenchSuite.Misc.Enumerate
import qualified BenchSuite.Misc.Floating
import qualified BenchSuite.Misc.ModelExtract
import qualified BenchSuite.Misc.Newtypes
import qualified BenchSuite.Misc.NoDiv0
import qualified BenchSuite.Misc.Polynomials
import qualified BenchSuite.Misc.SetAlgebra
import qualified BenchSuite.Misc.SoftConstrain
import qualified BenchSuite.Misc.Tuple

-- | Lists
import qualified BenchSuite.Lists.BoundedMutex
import qualified BenchSuite.Lists.Fibonacci
import qualified BenchSuite.Lists.Nested

-- | Strings
import qualified BenchSuite.Strings.RegexCrossword
import qualified BenchSuite.Strings.SQLInjection

-- | Existentials
import qualified BenchSuite.Existentials.CRCPolynomial
import qualified BenchSuite.Existentials.Diophantine

-- | Transformers
import qualified BenchSuite.Transformers.SymbolicEval


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
       , weakestPreconditions
       , optimizations
       , uninterpreted
       , proofTools
       , codeGeneration
       , crypto
       , misc
       , lists
       , strings
       , transformers
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


weakestPreconditions :: Benchmark
weakestPreconditions = bgroup "WeakestPreconditions" $ runBenchMark <$>
                       [ BenchSuite.WeakestPreconditions.Append.benchmarks
                       , BenchSuite.WeakestPreconditions.Basics.benchmarks
                       , BenchSuite.WeakestPreconditions.Fib.benchmarks
                       , BenchSuite.WeakestPreconditions.GCD.benchmarks
                       , BenchSuite.WeakestPreconditions.IntDiv.benchmarks
                       , BenchSuite.WeakestPreconditions.IntSqrt.benchmarks
                       , BenchSuite.WeakestPreconditions.Length.benchmarks
                       , BenchSuite.WeakestPreconditions.Sum.benchmarks
                       ]


optimizations :: Benchmark
optimizations = bgroup "Optimizations" $ runBenchMark <$>
                [ BenchSuite.Optimization.Enumerate.benchmarks
                , BenchSuite.Optimization.ExtField.benchmarks
                , BenchSuite.Optimization.LinearOpt.benchmarks
                , BenchSuite.Optimization.Production.benchmarks
                , BenchSuite.Optimization.VM.benchmarks
                ]


uninterpreted :: Benchmark
uninterpreted = bgroup "Uninterpreted" $ runBenchMark <$>
                [ BenchSuite.Uninterpreted.AUF.benchmarks
                , BenchSuite.Uninterpreted.Deduce.benchmarks
                , BenchSuite.Uninterpreted.Function.benchmarks
                , BenchSuite.Uninterpreted.Multiply.benchmarks
                , BenchSuite.Uninterpreted.Shannon.benchmarks
                , BenchSuite.Uninterpreted.Sort.benchmarks
                , BenchSuite.Uninterpreted.UISortAllSat.benchmarks
                ]


proofTools :: Benchmark
proofTools = bgroup "ProofTools" $ runBenchMark <$>
             [ BenchSuite.ProofTools.BMC.benchmarks
             , BenchSuite.ProofTools.Fibonacci.benchmarks
             , BenchSuite.ProofTools.Strengthen.benchmarks
             , BenchSuite.ProofTools.Sum.benchmarks
             ]


codeGeneration :: Benchmark
codeGeneration = bgroup "CodeGeneration" $ runBenchMark <$>
                 [ BenchSuite.CodeGeneration.AddSub.benchmarks
                 , BenchSuite.CodeGeneration.CRC_USB5.benchmarks
                 , BenchSuite.CodeGeneration.Fibonacci.benchmarks
                 , BenchSuite.CodeGeneration.GCD.benchmarks
                 , BenchSuite.CodeGeneration.PopulationCount.benchmarks
                 , BenchSuite.CodeGeneration.Uninterpreted.benchmarks
                 ]


crypto :: Benchmark
crypto = bgroup "Crypto" $ runBenchMark <$>
         [ BenchSuite.Crypto.AES.benchmarks
         , BenchSuite.Crypto.RC4.benchmarks
         , BenchSuite.Crypto.SHA.benchmarks
         ]


misc :: Benchmark
misc = bgroup "Miscellaneous" $ runBenchMark <$>
       [ BenchSuite.Misc.Auxiliary.benchmarks
       , BenchSuite.Misc.Enumerate.benchmarks
       , BenchSuite.Misc.Floating.benchmarks
       , BenchSuite.Misc.ModelExtract.benchmarks
       , BenchSuite.Misc.Newtypes.benchmarks
       , BenchSuite.Misc.NoDiv0.benchmarks
       , BenchSuite.Misc.Polynomials.benchmarks
       , BenchSuite.Misc.SetAlgebra.benchmarks
       , BenchSuite.Misc.SoftConstrain.benchmarks
       , BenchSuite.Misc.Tuple.benchmarks
       ]


lists :: Benchmark
lists = bgroup "Lists" $ runBenchMark <$>
        [ BenchSuite.Lists.BoundedMutex.benchmarks
        , BenchSuite.Lists.Fibonacci.benchmarks
        , BenchSuite.Lists.Nested.benchmarks
        ]


strings :: Benchmark
strings = bgroup "Strings" $ runBenchMark <$>
          [ BenchSuite.Strings.RegexCrossword.benchmarks
          , BenchSuite.Strings.SQLInjection.benchmarks
          ]


existentials :: Benchmark
existentials = bgroup "Existentials" $ runBenchMark <$>
               [ BenchSuite.Existentials.CRCPolynomial.benchmarks
               , BenchSuite.Existentials.Diophantine.benchmarks
               ]


transformers :: Benchmark
transformers = bgroup "Transformers" $ runBenchMark <$>
               [ BenchSuite.Transformers.SymbolicEval.benchmarks
               ]
