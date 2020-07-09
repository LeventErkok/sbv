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

import qualified Gauge.Main as G
import           Gauge.Main.Options (defaultConfig, Config(..))

import           Utils.SBVBenchFramework

import           BenchSuite.Bench.Bench

-- Puzzles
import qualified BenchSuite.Puzzles.Birthday
import qualified BenchSuite.Puzzles.Coins
-- import qualified BenchSuite.Puzzles.Counts -- see comment below
import qualified BenchSuite.Puzzles.DogCatMouse
import qualified BenchSuite.Puzzles.Euler185
import qualified BenchSuite.Puzzles.Garden
import qualified BenchSuite.Puzzles.LadyAndTigers
import qualified BenchSuite.Puzzles.MagicSquare
import qualified BenchSuite.Puzzles.NQueens
import qualified BenchSuite.Puzzles.SendMoreMoney
import qualified BenchSuite.Puzzles.Sudoku
import qualified BenchSuite.Puzzles.U2Bridge

-- BitPrecise
import qualified BenchSuite.BitPrecise.BitTricks
import qualified BenchSuite.BitPrecise.BrokenSearch
import qualified BenchSuite.BitPrecise.Legato
import qualified BenchSuite.BitPrecise.MergeSort
import qualified BenchSuite.BitPrecise.MultMask
import qualified BenchSuite.BitPrecise.PrefixSum

-- Queries
import qualified BenchSuite.Queries.AllSat
import qualified BenchSuite.Queries.CaseSplit
import qualified BenchSuite.Queries.Concurrency
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
import qualified BenchSuite.Misc.Floating
import qualified BenchSuite.Misc.ModelExtract
import qualified BenchSuite.Misc.Newtypes
import qualified BenchSuite.Misc.NoDiv0
import qualified BenchSuite.Misc.Polynomials
import qualified BenchSuite.Misc.SetAlgebra
import qualified BenchSuite.Misc.SoftConstrain
import qualified BenchSuite.Misc.Tuple

-- Lists
import qualified BenchSuite.Lists.BoundedMutex
import qualified BenchSuite.Lists.Fibonacci
import qualified BenchSuite.Lists.Nested

-- Strings
import qualified BenchSuite.Strings.RegexCrossword
import qualified BenchSuite.Strings.SQLInjection

-- Existentials
import qualified BenchSuite.Existentials.CRCPolynomial
import qualified BenchSuite.Existentials.Diophantine

-- Transformers
import qualified BenchSuite.Transformers.SymbolicEval

-- | Custom config to limit benchmarks to 2 minutes of runtime. This is required
-- because we can easily generate benchmarks that take a lot of wall time to
-- solve, especially with 'Data.SBV.allSatWith' calls
benchConfig :: Config
benchConfig = defaultConfig { timeLimit = Just 1.00 }

{-
To benchmark sbv we require two use cases: For continuous integration we want a
snapshot of all benchmarks at a given point in time and we want to be able to
compare benchmarks over time for performance tuning. For this module we default
to the continuous integration flow, thus 'cabal bench' this will get a timestamp
for the file, e.g., '2020-06-27-15:54:05.447753608-UTC.csv', run the benchmarks
and output the statistics to that file in 'sbv/BenchSuite/BenchFiles\/'. The
workflow for fine grained performance analysis is to run a benchmark, make your
changes, then rerun the benchmark. We analyze these results using the
<http://hackage.haskell.org/package/bench-show-0.3.1 bench-show> package, which
expects subsequent runs in the same file, thus you'll need to change the file
name to something other then a UTC time stamp. To only run one or a few
benchmarks we use the '--match' command from the
<https://hackage.haskell.org/package/gauge-0.2.5 gauge> library. For example to
run only NQueens you would do the following: `cabal build SBVBench; ./SBVBench
--match=pattern -- 'NQueens'`. Note that comparisons with benchmarks run on
different machines will be spurious so use your best judgment.
-}
main :: IO ()
main = do
  -- generate the benchmark file name
  f <- benchResultsFile <$> timeStamp

  -- run the benchmarks
  G.defaultMainWith benchConfig {csvFile = Just f} $
       [ puzzles
       , bitPrecise
         -- queries are not running with overHead
       -- , queries
       , weakestPreconditions
       , optimizations
       , uninterpreted
       , proofTools
       -- code generation takes too much time and memory
       -- , codeGeneration
       -- crypto also is too expensive
       -- crypto
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
 --                , BenchSuite.Puzzles.Counts.benchmarks
                   , BenchSuite.Puzzles.Birthday.benchmarks
                   , BenchSuite.Puzzles.DogCatMouse.benchmarks
                   , BenchSuite.Puzzles.Euler185.benchmarks
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

-- | We call `runOverheadBenchmark` run the benchmarks with both sbv and z3
-- native on the same program. To construct a benchmark for only sbv one would
-- call `runBenchmark`
puzzles :: Benchmark
puzzles = bgroup "Puzzles" $ runOverheadBenchmark <$> puzzleBenchmarks


--------------------------- BitPrecise ------------------------------------------
bitPreciseBenchmarks :: [Runner]
bitPreciseBenchmarks = [ BenchSuite.BitPrecise.BitTricks.benchmarks
                       -- , BenchSuite.BitPrecise.BrokenSearch.benchmarks
                       -- , BenchSuite.BitPrecise.Legato.benchmarks
                       -- , BenchSuite.BitPrecise.MergeSort.benchmarks
                       , BenchSuite.BitPrecise.MultMask.benchmarks
                       , BenchSuite.BitPrecise.PrefixSum.benchmarks
                       ]

bitPrecise :: Benchmark
bitPrecise = bgroup "BitPrecise" $ runOverheadBenchmark <$> bitPreciseBenchmarks


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
queries = bgroup "Queries" $ runOverheadBenchmark <$> queryBenchmarks


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
  runOverheadBenchmark <$> weakestPreconditionBenchmarks


--------------------------- Optimizations ---------------------------------------
optimizationBenchmarks :: [Runner]
optimizationBenchmarks = [ BenchSuite.Optimization.Enumerate.benchmarks
                         , BenchSuite.Optimization.ExtField.benchmarks
                         , BenchSuite.Optimization.LinearOpt.benchmarks
                         , BenchSuite.Optimization.Production.benchmarks
                         , BenchSuite.Optimization.VM.benchmarks
                         ]

optimizations :: Benchmark
optimizations = bgroup "Optimizations" $ runOverheadBenchmark <$> optimizationBenchmarks


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
uninterpreted = bgroup "Uninterpreted" $ runOverheadBenchmark <$> uninterpretedBenchmarks


--------------------------- ProofTools -----------------------------------------
proofToolBenchmarks :: [Runner]
proofToolBenchmarks = [ BenchSuite.ProofTools.BMC.benchmarks
                      , BenchSuite.ProofTools.Fibonacci.benchmarks
                      , BenchSuite.ProofTools.Strengthen.benchmarks
                      , BenchSuite.ProofTools.Sum.benchmarks
                      ]

proofTools :: Benchmark
proofTools = bgroup "ProofTools" $ runOverheadBenchmark <$> proofToolBenchmarks


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
                 runOverheadBenchmark <$> codeGenerationBenchmarks


--------------------------- Crypto ----------------------------------------------
cryptoBenchmarks :: [Runner]
cryptoBenchmarks = [ BenchSuite.Crypto.AES.benchmarks
                   , BenchSuite.Crypto.RC4.benchmarks
                   , BenchSuite.Crypto.SHA.benchmarks
                   ]

crypto :: Benchmark
crypto = bgroup "Crypto" $ runOverheadBenchmark <$> cryptoBenchmarks


--------------------------- Miscellaneous ---------------------------------------
miscBenchmarks :: [Runner]
miscBenchmarks = [ BenchSuite.Misc.Auxiliary.benchmarks
                 , BenchSuite.Misc.Enumerate.benchmarks
                 , BenchSuite.Misc.Floating.benchmarks
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
misc = bgroup "Miscellaneous" $ runOverheadBenchmark <$> miscBenchmarks


--------------------------- Lists -----------------------------------------------
listBenchmarks :: [Runner]
listBenchmarks = [ BenchSuite.Lists.BoundedMutex.benchmarks
                 , BenchSuite.Lists.Fibonacci.benchmarks
                 , BenchSuite.Lists.Nested.benchmarks
                 ]

lists :: Benchmark
lists = bgroup "Lists" $ runOverheadBenchmark <$> listBenchmarks


--------------------------- Strings ---------------------------------------------
stringBenchmarks :: [Runner]
stringBenchmarks = [ BenchSuite.Strings.RegexCrossword.benchmarks
                   , BenchSuite.Strings.SQLInjection.benchmarks
                   ]

strings :: Benchmark
strings = bgroup "Strings" $ runOverheadBenchmark <$> stringBenchmarks


--------------------------- Existentials ----------------------------------------
existentialBenchmarks :: [Runner]
existentialBenchmarks = [ BenchSuite.Existentials.CRCPolynomial.benchmarks
                        , BenchSuite.Existentials.Diophantine.benchmarks
                        ]

existentials :: Benchmark
existentials = bgroup "Existentials" $ runOverheadBenchmark <$> existentialBenchmarks


--------------------------- Transformers ----------------------------------------
transformerBenchmarks :: [Runner]
transformerBenchmarks = [ BenchSuite.Transformers.SymbolicEval.benchmarks
                        ]

transformers :: Benchmark
transformers = bgroup "Transformers" $ runOverheadBenchmark <$> transformerBenchmarks
