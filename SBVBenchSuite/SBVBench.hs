-----------------------------------------------------------------------------
-- |
-- Module    : SBVBench
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Entry point to benchmark SBV. We define this as a separate cabal target so
-- that performance regressions can continue to occur as other fine-tuning
-- happens in parallel
-----------------------------------------------------------------------------

module Main where

import           Test.Tasty hiding (defaultMain)
import           Test.Tasty.Bench

import           BenchSuite.Bench.Bench

-- Puzzles
import qualified BenchSuite.Puzzles.Birthday
import qualified BenchSuite.Puzzles.Coins
-- import qualified BenchSuite.Puzzles.Counts -- see comment below
import qualified BenchSuite.Puzzles.DogCatMouse
-- import qualified BenchSuite.Puzzles.Euler185
import qualified BenchSuite.Puzzles.Garden
import qualified BenchSuite.Puzzles.LadyAndTigers
import qualified BenchSuite.Puzzles.MagicSquare
import qualified BenchSuite.Puzzles.NQueens
import qualified BenchSuite.Puzzles.SendMoreMoney
import qualified BenchSuite.Puzzles.Sudoku
-- import qualified BenchSuite.Puzzles.U2Bridge

-- BitPrecise
import qualified BenchSuite.BitPrecise.BitTricks
-- import qualified BenchSuite.BitPrecise.BrokenSearch
-- import qualified BenchSuite.BitPrecise.Legato
-- import qualified BenchSuite.BitPrecise.MergeSort
-- import qualified BenchSuite.BitPrecise.MultMask
-- import qualified BenchSuite.BitPrecise.PrefixSum

-- Queries
import qualified BenchSuite.Queries.AllSat
import qualified BenchSuite.Queries.CaseSplit
-- import qualified BenchSuite.Queries.Concurrency
import qualified BenchSuite.Queries.Enums
import qualified BenchSuite.Queries.FourFours
import qualified BenchSuite.Queries.GuessNumber
import qualified BenchSuite.Queries.Interpolants
import qualified BenchSuite.Queries.UnsatCore

-- Weakest Preconditions
import qualified BenchSuite.WeakestPreconditions.Append
import qualified BenchSuite.WeakestPreconditions.Basics
import qualified BenchSuite.WeakestPreconditions.Fib
import qualified BenchSuite.WeakestPreconditions.GCD
import qualified BenchSuite.WeakestPreconditions.IntDiv
import qualified BenchSuite.WeakestPreconditions.IntSqrt
import qualified BenchSuite.WeakestPreconditions.Length
import qualified BenchSuite.WeakestPreconditions.Sum

-- Optimization
import qualified BenchSuite.Optimization.Enumerate
import qualified BenchSuite.Optimization.ExtField
import qualified BenchSuite.Optimization.LinearOpt
import qualified BenchSuite.Optimization.Production
import qualified BenchSuite.Optimization.VM

-- Uninterpreted
import qualified BenchSuite.Uninterpreted.AUF
import qualified BenchSuite.Uninterpreted.Deduce
import qualified BenchSuite.Uninterpreted.Function
import qualified BenchSuite.Uninterpreted.Multiply
import qualified BenchSuite.Uninterpreted.Shannon
import qualified BenchSuite.Uninterpreted.Sort
import qualified BenchSuite.Uninterpreted.UISortAllSat

-- Proof Tools
import qualified BenchSuite.ProofTools.BMC
import qualified BenchSuite.ProofTools.Fibonacci
import qualified BenchSuite.ProofTools.Strengthen
import qualified BenchSuite.ProofTools.Sum

-- Code Generation
import qualified BenchSuite.CodeGeneration.AddSub
import qualified BenchSuite.CodeGeneration.CRC_USB5
import qualified BenchSuite.CodeGeneration.Fibonacci
import qualified BenchSuite.CodeGeneration.GCD
import qualified BenchSuite.CodeGeneration.PopulationCount
import qualified BenchSuite.CodeGeneration.Uninterpreted

-- Crypto
import qualified BenchSuite.Crypto.AES
import qualified BenchSuite.Crypto.RC4
import qualified BenchSuite.Crypto.SHA

-- Miscellaneous
import qualified BenchSuite.Misc.Auxiliary
import qualified BenchSuite.Misc.Enumerate
-- import qualified BenchSuite.Misc.Floating
import qualified BenchSuite.Misc.ModelExtract
import qualified BenchSuite.Misc.Newtypes
import qualified BenchSuite.Misc.NoDiv0
-- import qualified BenchSuite.Misc.Polynomials
import qualified BenchSuite.Misc.SetAlgebra
import qualified BenchSuite.Misc.SoftConstrain
import qualified BenchSuite.Misc.Tuple

-- Lists
import qualified BenchSuite.Lists.BoundedMutex
import qualified BenchSuite.Lists.Fibonacci

-- Strings
import qualified BenchSuite.Strings.RegexCrossword
import qualified BenchSuite.Strings.SQLInjection

-- Existentials
-- import qualified BenchSuite.Existentials.CRCPolynomial
import qualified BenchSuite.Existentials.Diophantine

-- Transformers
import qualified BenchSuite.Transformers.SymbolicEval


{-
To benchmark sbv we require two use cases: For continuous integration we want a
snapshot of all benchmarks at a given point in time and we want to be able to
compare benchmarks over time for performance tuning. For this module we default
to the continuous integration flow. The workflow for fine grained performance
analysis is to run a benchmark, make your changes, then rerun the benchmark. See
<https://hackage.haskell.org/package/tasty-bench> package, for instructions on
comparing benchmarks, using patterns to run a single benchmark or log results to
a file. Furthermore, we provide a few utility functions to ease the details in
benchmarking standalone z3 programs and sbv programs in Utils.SBVBenchFramework.
`cabal build SBVBench; ./SBVBench --match=pattern -- 'NQueens'`. Note that
comparisons with benchmarks run on different machines will be spurious so use
your best judgment.
-}
main :: IO ()
main = do
  -- timeout is set to 2 minutes
  let timeout    = localOption (mkTimeout 120000000)
      opts       = [timeout]
      setOptions :: Benchmark -> Benchmark
      setOptions = foldr (.) id opts

  -- run the benchmarks
  defaultMain
    $ setOptions <$> [ puzzles
                     , bitPrecise
                     , queries
                     , weakestPreconditions
                     , optimizations
                     , uninterpreted
                     , proofTools
                     -- , codeGeneration :NOTE code generation takes too much time and memory
                     -- crypto :NOTE crypto also is too expensive
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

--------------------------- Puzzles ---------------------------------------------
puzzleBenchmarks :: [Runner]
puzzleBenchmarks = [ BenchSuite.Puzzles.Coins.benchmarks
                   -- disable Counts for now, there is some issue with the counts function
                   -- in a repl it works fine, when compiled it does not terminate
                   -- , BenchSuite.Puzzles.Counts.benchmarks
                   , BenchSuite.Puzzles.Birthday.benchmarks
                   , BenchSuite.Puzzles.DogCatMouse.benchmarks
                   -- expensive
                   -- , BenchSuite.Puzzles.Euler185.benchmarks
                   , BenchSuite.Puzzles.Garden.benchmarks
                   , BenchSuite.Puzzles.LadyAndTigers.benchmarks
                   , BenchSuite.Puzzles.SendMoreMoney.benchmarks
                   , BenchSuite.Puzzles.NQueens.benchmarks
                   , BenchSuite.Puzzles.MagicSquare.benchmarks
                   , BenchSuite.Puzzles.Sudoku.benchmarks
                   -- TODO: sbv finishes cnt3 in 100s but z3 does so in 83 ms,
                   -- probably an issue with z3 here ,
                   -- BenchSuite.Puzzles.U2Bridge.benchmarks
                   ]

puzzles :: Benchmark
puzzles = bgroup "Puzzles" $ runBenchmark <$> puzzleBenchmarks


--------------------------- BitPrecise ------------------------------------------
bitPreciseBenchmarks :: [Runner]
bitPreciseBenchmarks = [ BenchSuite.BitPrecise.BitTricks.benchmarks
                       -- These benchmarks blow the stack :TODO fix them
                       -- , BenchSuite.BitPrecise.BrokenSearch.benchmarks
                       -- , BenchSuite.BitPrecise.Legato.benchmarks
                       -- , BenchSuite.BitPrecise.MergeSort.benchmarks
                       -- , BenchSuite.BitPrecise.MultMask.benchmarks
                       -- expensive
                       -- , BenchSuite.BitPrecise.PrefixSum.benchmarks
                       ]

bitPrecise :: Benchmark
bitPrecise = bgroup "BitPrecise" $ runBenchmark <$> bitPreciseBenchmarks


--------------------------- Query -----------------------------------------------
queryBenchmarks :: [Runner]
queryBenchmarks = [ BenchSuite.Queries.AllSat.benchmarks
                  , BenchSuite.Queries.CaseSplit.benchmarks
                  -- The concurrency demo has STM blocking when benchmarking
                  -- , BenchSuite.Queries.Concurrency.benchmarks
                  , BenchSuite.Queries.Enums.benchmarks
                  , BenchSuite.Queries.FourFours.benchmarks
                  , BenchSuite.Queries.GuessNumber.benchmarks
                  , BenchSuite.Queries.Interpolants.benchmarks
                  , BenchSuite.Queries.UnsatCore.benchmarks
                  ]

queries :: Benchmark
queries = bgroup "Queries" $ runBenchmark <$> queryBenchmarks


--------------------------- WeakestPreconditions --------------------------------
weakestPreconditionBenchmarks :: [Runner]
weakestPreconditionBenchmarks =
  [ BenchSuite.WeakestPreconditions.Append.benchmarks
  , BenchSuite.WeakestPreconditions.Basics.benchmarks
  , BenchSuite.WeakestPreconditions.Fib.benchmarks
  , BenchSuite.WeakestPreconditions.GCD.benchmarks
  , BenchSuite.WeakestPreconditions.IntDiv.benchmarks
  , BenchSuite.WeakestPreconditions.IntSqrt.benchmarks
  , BenchSuite.WeakestPreconditions.Length.benchmarks
  , BenchSuite.WeakestPreconditions.Sum.benchmarks
  ]

weakestPreconditions :: Benchmark
weakestPreconditions = bgroup "WeakestPreconditions" $
  runBenchmark <$> weakestPreconditionBenchmarks


--------------------------- Optimizations ---------------------------------------
optimizationBenchmarks :: [Runner]
optimizationBenchmarks = [ BenchSuite.Optimization.Enumerate.benchmarks
                         , BenchSuite.Optimization.ExtField.benchmarks
                         , BenchSuite.Optimization.LinearOpt.benchmarks
                         , BenchSuite.Optimization.Production.benchmarks
                         , BenchSuite.Optimization.VM.benchmarks
                         ]

optimizations :: Benchmark
optimizations = bgroup "Optimizations" $ runBenchmark <$> optimizationBenchmarks


--------------------------- Uninterpreted ---------------------------------------
uninterpretedBenchmarks :: [Runner]
uninterpretedBenchmarks = [ BenchSuite.Uninterpreted.AUF.benchmarks
                          , BenchSuite.Uninterpreted.Deduce.benchmarks
                          , BenchSuite.Uninterpreted.Function.benchmarks
                          , BenchSuite.Uninterpreted.Multiply.benchmarks
                          , BenchSuite.Uninterpreted.Shannon.benchmarks
                          , BenchSuite.Uninterpreted.Sort.benchmarks
                          , BenchSuite.Uninterpreted.UISortAllSat.benchmarks
                          ]

uninterpreted :: Benchmark
uninterpreted = bgroup "Uninterpreted" $ runBenchmark <$> uninterpretedBenchmarks


--------------------------- ProofTools -----------------------------------------
proofToolBenchmarks :: [Runner]
proofToolBenchmarks = [ BenchSuite.ProofTools.BMC.benchmarks
                      , BenchSuite.ProofTools.Fibonacci.benchmarks
                      , BenchSuite.ProofTools.Strengthen.benchmarks
                      , BenchSuite.ProofTools.Sum.benchmarks
                      ]

proofTools :: Benchmark
proofTools = bgroup "ProofTools" $ runBenchmark <$> proofToolBenchmarks


--------------------------- Code Generation -------------------------------------
codeGenerationBenchmarks :: [Runner]
codeGenerationBenchmarks = [ BenchSuite.CodeGeneration.AddSub.benchmarks
                           , BenchSuite.CodeGeneration.CRC_USB5.benchmarks
                           , BenchSuite.CodeGeneration.Fibonacci.benchmarks
                           , BenchSuite.CodeGeneration.GCD.benchmarks
                           , BenchSuite.CodeGeneration.PopulationCount.benchmarks
                           , BenchSuite.CodeGeneration.Uninterpreted.benchmarks
                           ]

codeGeneration :: Benchmark
codeGeneration = bgroup "CodeGeneration" $
                 runBenchmark <$> codeGenerationBenchmarks


--------------------------- Crypto ----------------------------------------------
cryptoBenchmarks :: [Runner]
cryptoBenchmarks = [ BenchSuite.Crypto.AES.benchmarks
                   , BenchSuite.Crypto.RC4.benchmarks
                   , BenchSuite.Crypto.SHA.benchmarks
                   ]

crypto :: Benchmark
crypto = bgroup "Crypto" $ runBenchmark <$> cryptoBenchmarks


--------------------------- Miscellaneous ---------------------------------------
miscBenchmarks :: [Runner]
miscBenchmarks = [ BenchSuite.Misc.Auxiliary.benchmarks
                 , BenchSuite.Misc.Enumerate.benchmarks
                 -- expensive
                 -- , BenchSuite.Misc.Floating.benchmarks
                 , BenchSuite.Misc.ModelExtract.benchmarks
                 , BenchSuite.Misc.Newtypes.benchmarks
                 , BenchSuite.Misc.NoDiv0.benchmarks
                 -- killed by OS, TODO: Investigate
                 -- , BenchSuite.Misc.Polynomials.benchmarks
                 , BenchSuite.Misc.SetAlgebra.benchmarks
                 , BenchSuite.Misc.SoftConstrain.benchmarks
                 , BenchSuite.Misc.Tuple.benchmarks
                 ]

misc :: Benchmark
misc = bgroup "Miscellaneous" $ runBenchmark <$> miscBenchmarks


--------------------------- Lists -----------------------------------------------
listBenchmarks :: [Runner]
listBenchmarks = [ BenchSuite.Lists.BoundedMutex.benchmarks
                 , BenchSuite.Lists.Fibonacci.benchmarks
                 ]

lists :: Benchmark
lists = bgroup "Lists" $ runBenchmark <$> listBenchmarks


--------------------------- Strings ---------------------------------------------
stringBenchmarks :: [Runner]
stringBenchmarks = [ BenchSuite.Strings.RegexCrossword.benchmarks
                   , BenchSuite.Strings.SQLInjection.benchmarks
                   ]

strings :: Benchmark
strings = bgroup "Strings" $ runBenchmark <$> stringBenchmarks


--------------------------- Existentials ----------------------------------------
existentialBenchmarks :: [Runner]
existentialBenchmarks = [ -- BenchSuite.Existentials.CRCPolynomial.benchmarks
                          BenchSuite.Existentials.Diophantine.benchmarks
                        ]

existentials :: Benchmark
existentials = bgroup "Existentials" $ runBenchmark <$> existentialBenchmarks


--------------------------- Transformers ----------------------------------------
transformerBenchmarks :: [Runner]
transformerBenchmarks = [ BenchSuite.Transformers.SymbolicEval.benchmarks
                        ]

transformers :: Benchmark
transformers = bgroup "Transformers" $ runBenchmark <$> transformerBenchmarks
