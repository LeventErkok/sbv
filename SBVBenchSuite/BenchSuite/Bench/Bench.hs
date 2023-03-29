-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Bench.Bench
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Assessing the overhead of calling solving examples via sbv vs individual solvers
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module BenchSuite.Bench.Bench
  ( run
  , run'
  , runWith
  , runIOWith
  , runIO
  , runPure
  , rGroup
  , runBenchmark
  , onConfig
  , onDesc
  , runner
  , onProblem
  , Runner(..)
  , using
  ) where

import           Control.DeepSeq         (NFData (..), rwhnf)

import qualified Test.Tasty.Bench        as B
import qualified Utils.SBVBenchFramework as U

-- | The type of the problem to benchmark. This allows us to operate on Runners
-- as values themselves yet still have a unified interface with gauge.
data Problem = forall a . (U.Provable a, U.Satisfiable a) => Problem a

-- | Similarly to Problem, BenchResult is boilerplate for a nice api
data BenchResult = forall a . (Show a, NFData a) => BenchResult a

-- | A runner is anything that allows the solver to solve, such as:
-- 'Data.SBV.proveWith' or 'Data.SBV.satWith'. We utilize existential types to
-- lose type information and create a unified interface with gauge. We
-- require a runner in order to generate a 'Data.SBV.transcript' and then to run
-- the actual benchmark. We bundle this redundantly into a record so that the
-- benchmarks can be defined in each respective module, with the run function
-- that makes sense for that problem, and then redefined in 'SBVBench'. This is
-- useful because problems that require 'Data.SBV.allSatWith' can lead to a lot
-- of variance in the benchmarking data. Single benchmark runners like
-- 'Data.SBV.satWith' and 'Data.SBV.proveWith' work best.
data RunnerI = RunnerI { runI        :: U.SMTConfig -> Problem -> IO BenchResult
                       , config      :: U.SMTConfig
                       , description :: String
                       , problem     :: Problem
                       }

-- | GADT to allow arbitrary nesting of runners. This copies criterion's design
-- so that we don't have to separate out runners that run a single benchmark
-- from runners that need to run several benchmarks
data Runner where
  RBenchmark  :: B.Benchmark -> Runner   -- ^ a wrapper around tasty-bench benchmarks
  Runner      :: RunnerI     -> Runner   -- ^ a single run
  RunnerGroup :: [Runner]    -> Runner   -- ^ a group of runs

-- | Convenience boilerplate functions, simply avoiding a lens dependency
using :: Runner -> (Runner -> Runner) -> Runner
using = flip ($)
{-# INLINE using #-}

-- | Set the runner function
runner :: (Show c, NFData c) =>
  (forall a. (U.Provable a, U.Satisfiable a) => U.SMTConfig -> a -> IO c) -> Runner -> Runner
runner r' (Runner r@RunnerI{}) = Runner $ r{runI = toRun r'}
runner r' (RunnerGroup rs)     = RunnerGroup $ runner r' <$> rs
runner _  x                    = x
{-# INLINE runner #-}

toRun :: (Show c, NFData c) =>
  (forall a. (U.Provable a, U.Satisfiable a) => U.SMTConfig -> a -> IO c)
  -> U.SMTConfig
  -> Problem
  -> IO BenchResult
toRun f c p = BenchResult <$> helper p
  -- similar to helper in onProblem, this is lmap from profunctor land, i.e., we
  -- curry with a config, then change the runner function from (a -> IO c), to
  -- (Problem -> IO c)
  where helper (Problem a) = f c a
{-# INLINE toRun #-}

onConfig :: (U.SMTConfig -> U.SMTConfig) -> RunnerI -> RunnerI
onConfig f r@RunnerI{..} = r{config = f config}
{-# INLINE onConfig #-}

onDesc :: (String -> String) -> RunnerI -> RunnerI
onDesc f r@RunnerI{..} = r{description = f description}
{-# INLINE onDesc #-}

onProblem :: (forall a. a -> a) -> RunnerI -> RunnerI
onProblem f r@RunnerI{..} = r{problem = helper problem}
  where
    -- helper function to avoid profunctor dependency, this is simply fmap, or
    -- rmap for profunctor land
    helper :: Problem -> Problem
    helper (Problem p) = Problem $ f p
{-# INLINE onProblem #-}

-- | make a normal benchmark without the overhead comparison. Notice this is
-- just unpacking the Runner record
mkBenchmark :: RunnerI -> B.Benchmark
mkBenchmark RunnerI{..} = B.bench description . B.nfIO $! runI config problem
{-# INLINE  mkBenchmark #-}

-- | Convert a Runner or a group of Runners to Benchmarks, this is an api level
-- function to convert the runners defined in each file to benchmarks which can
-- be run by gauge
runBenchmark :: Runner -> B.Benchmark
runBenchmark (Runner r@RunnerI{}) = mkBenchmark r
runBenchmark (RunnerGroup rs)     = B.bgroup "" $ runBenchmark <$> rs
runBenchmark (RBenchmark b)       = b
{-# INLINE runBenchmark #-}

-- | This is just a wrapper around the RunnerI constructor and serves as the main
-- entry point to make a runner for a user in case they need something custom.
run' :: (NFData b, Show b) =>
  (forall a. (U.Provable a, U.Satisfiable a) => U.SMTConfig -> a -> IO b)
  -> U.SMTConfig
  -> String
  -> Problem
  -> Runner
run' r config description problem = Runner $ RunnerI{..}
  where runI = toRun r
{-# INLINE run' #-}

-- | Convenience function for creating benchmarks that exposes a configuration
runWith :: (U.Provable a, U.Satisfiable a) => U.SMTConfig -> String -> a -> Runner
runWith c d p = run' U.satWith c d (Problem p)
{-# INLINE runWith #-}

-- | Main entry point for simple benchmarks. See 'mkRunner'' or 'mkRunnerWith'
-- for versions of this function that allows custom inputs. If you have some use
-- case that is not considered then you can simply overload the record fields.
run :: (U.Provable a, U.Satisfiable a) => String -> a -> Runner
run d p = runWith U.z3 d p `using` runner U.satWith
{-# INLINE run #-}

-- | Entry point for problems that return IO or to benchmark IO results
runIOWith :: NFData a => (a -> B.Benchmarkable) -> String -> a -> Runner
runIOWith f d = RBenchmark . B.bench d . f
{-# INLINE runIOWith #-}

-- | Benchmark an IO result of sbv, this could be codegen, return models, etc..
-- See @runIOWith@ for a version which allows the consumer to select the
-- Benchmarkable injection function
runIO :: NFData a => String -> IO a -> Runner
runIO d = RBenchmark . B.bench d . B.nfIO -- . silence
{-# INLINE runIO #-}

-- | Benchmark an pure result
runPure :: NFData a => String -> (a -> b) -> a -> Runner
runPure d = (RBenchmark . B.bench d) .: B.whnf
  where (.:) = (.).(.)
{-# INLINE runPure  #-}

-- | create a runner group. Useful for benchmarks that need to run several
-- benchmarks. See 'BenchSuite.Puzzles.NQueens' for an example.
rGroup :: [Runner] -> Runner
rGroup = RunnerGroup
{-# INLINE rGroup #-}

-- | Orphaned instances just for benchmarking
instance NFData U.AllSatResult where
  rnf (U.AllSatResult a b c results) =
    rnf a `seq` rnf b `seq` rnf c `seq` rwhnf results

-- | Unwrap the existential type to make gauge happy
instance NFData BenchResult where rnf (BenchResult a) = rnf a
