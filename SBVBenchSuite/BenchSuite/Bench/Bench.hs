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
  , runOverheadBenchMark
  , runBenchMark
  , onConfig
  , onDesc
  , runner
  , onProblem
  , Runner(..)
  , using
  ) where

import           Control.DeepSeq         (NFData (..), rwhnf)
import           System.Directory        (getCurrentDirectory)
import           System.IO
import           System.IO.Silently      (silence)

import           Gauge.Main

import qualified System.Process          as P
import qualified Utils.SBVBenchFramework as U

-- | The type of the problem to benchmark. This allows us to operate on Runners
-- as values themselves yet still have a unified interface with gauge.
data Problem = forall a . U.Provable a => Problem a

-- | Similarly to Problem, BenchResult is boilerplate for a nice api
data BenchResult = forall a . (Show a, NFData a) => BenchResult a

-- | A bench unit is a solver and a problem that represents an input problem
-- for the solver to solve
type BenchUnit = (U.SMTConfig, FilePath)

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
data RunnerI = RunnerI { runI        :: (U.SMTConfig -> Problem -> IO BenchResult)
                       , config      :: U.SMTConfig
                       , description :: String
                       , problem     :: Problem
                       }

-- | GADT to allow arbritrary nesting of runners. This copies criterion's design
-- so that we don't have to separate out runners that run a single benchmark
-- from runners that need to run several benchmarks
data Runner where
  RBenchmark  :: Benchmark -> Runner    -- ^ a wrapper around gauge benchmarks
  Runner      :: RunnerI   -> Runner    -- ^ a single run
  RunnerGroup :: [Runner]  -> Runner    -- ^ a group of runs

-- | Convenience boilerplate functions, simply avoiding a lens dependency
using :: Runner -> (Runner -> Runner) -> Runner
using = flip ($)

-- | Set the runner function
runner :: (Show c, NFData c) =>
  (forall a. U.Provable a => U.SMTConfig -> a -> IO c) -> Runner -> Runner
runner r' (Runner r@RunnerI{..}) = Runner $ r{runI = toRun r'}
runner r' (RunnerGroup rs)       = RunnerGroup $ runner r' <$> rs
runner _  x                      = x

toRun :: (Show c, NFData c) =>
  (forall a. U.Provable a => U.SMTConfig -> a -> IO c)
  -> U.SMTConfig
  -> Problem
  -> IO BenchResult
toRun f c p = BenchResult <$> helper p
  -- similar to helper in onProblem, this is lmap from profunctor land, i.e., we
  -- curry with a config, then change the runner function from (a -> IO c), to
  -- (Problem -> IO c)
  where helper (Problem a) = f c a

onConfig :: (U.SMTConfig -> U.SMTConfig) -> RunnerI -> RunnerI
onConfig f r@RunnerI{..} = r{config = f config}

onDesc :: (String -> String) -> RunnerI -> RunnerI
onDesc f r@RunnerI{..} = r{description = f description}

onProblem :: (forall a. a -> a) -> RunnerI -> RunnerI
onProblem f r@RunnerI{..} = r{problem = (helper problem)}
  where
    -- helper function to avoid profunctor dependency, this is simply fmap, or
    -- rmap for profunctor land
    helper :: Problem -> Problem
    helper (Problem p) = Problem $ f p


-- | Filepath to /dev/null
devNull :: FilePath
#ifndef WINDOWS
devNull = "/dev/null"
#else
devNull = "NUL"
#endif

-- | to bench a solver without interfacing through SBV we call transcript to
-- have SBV generate the input file for the solver and then create a process to
-- initiate execution on the solver. Note that we redirect stdout to /dev/devNull
-- or NUL on windows
runStandaloneSolver :: BenchUnit -> IO ()
runStandaloneSolver (slvr, fname) =
  withFile devNull WriteMode $
  (\h -> do (_,_,_,ph) <- P.createProcess (P.shell command){P.std_out = P.UseHandle h}
            _ <- P.waitForProcess ph
            return ())
  where command = U.mkExecString slvr fname

-- | Given a file name, a solver config, and a problem to solve, create an
-- environment for the gauge benchmark by generating a transcript file
standaloneEnv :: RunnerI -> IO FilePath -> IO BenchUnit
standaloneEnv RunnerI{..} f = f >>= go problem
  where
    -- generate a transcript for the unit
    go p file = do pwd <- getCurrentDirectory
                   let fPath = mconcat [pwd,"/",file]
                   _ <- runI config{U.transcript = Just fPath} p >> return ()
                   return (config,fPath)

-- | Cleanup the environment created by gauge by removing the transcript file
-- used to run the standalone solver
standaloneCleanup :: BenchUnit -> IO ()
standaloneCleanup (_,fPath) =  P.callCommand $ "rm " ++ fPath

-- | To construct a benchmark to test SBV's overhead we setup an environment
-- with gauge where a symbolic computation is emitted to a transcript file.
-- To test the solver without respect to SBV (standalone) we pass the transcript
-- file to the solver using the same primitives SBV does. Not that mkFileName
-- generates a random filename that is removed at the end of the benchmark. This
-- function exposes the solver and the solve interface in case the user would
-- like to benchmark with something other than 'Data.SBV.z3' and so that we can
-- benchmark all solving variants, e.g., 'Data.SBV.proveWith',
-- 'Data.SBV.satWith', 'Data.SBV.allProveWith' etc.
mkOverheadBenchMark' :: RunnerI -> Benchmark
mkOverheadBenchMark' r@RunnerI{..} =
  envWithCleanup
  (standaloneEnv r U.mkFileName)
  standaloneCleanup $
  \ ~unit ->
    bgroup description [ bench "standalone" $ nfIO $ runStandaloneSolver unit
                       -- notice for sbv benchmark; we pull the solver out of unit and
                       -- use the input problem not the transcript in the unit
                       , bench "sbv"        $ nfIO $ runI (fst unit) problem
                       ]

runOverheadBenchMark :: Runner -> Benchmark
runOverheadBenchMark (Runner r@RunnerI{..}) = mkOverheadBenchMark' r
runOverheadBenchMark (RunnerGroup rs)       = bgroup "" $ -- leave the description close to the benchmark/problem definition
                                             runOverheadBenchMark <$> rs
runOverheadBenchMark (RBenchmark b)         = b


-- | make a normal benchmark without the overhead comparision. Notice this is
-- just unpacking the Runner record
mkBenchMark :: RunnerI -> Benchmark
mkBenchMark RunnerI{..} = bgroup description [bench "" . nfIO $! runI config problem]

-- | Convert a Runner or a group of Runners to Benchmarks, this is an api level
-- function to convert the runners defined in each file to benchmarks which can
-- be run by gauge
runBenchMark :: Runner -> Benchmark
runBenchMark (Runner r@RunnerI{..}) = mkBenchMark r
runBenchMark (RunnerGroup rs)       = bgroup "" $ runBenchMark <$> rs
runBenchMark (RBenchmark b)         = b

-- | This is just a wrapper around the RunnerI constructor and serves as the main
-- entry point to make a runner for a user in case they need something custom.
run' :: (NFData b, Show b) =>
  (forall a. U.Provable a => U.SMTConfig -> a -> IO b)
  -> U.SMTConfig
  -> String
  -> Problem
  -> Runner
run' r config description problem = Runner $ RunnerI{..}
  where runI = toRun r

-- | Convenience function for creating benchmarks that exposes a configuration
runWith :: U.Provable a => U.SMTConfig -> String -> a -> Runner
runWith c d p = run' U.satWith c d (Problem p)

-- | Main entry point for simple benchmarks. See 'mkRunner'' or 'mkRunnerWith'
-- for versions of this function that allows custom inputs. If you have some use
-- case that is not considered then you can simply overload the record fields.
run :: U.Provable a => String -> a -> Runner
run d p = runWith U.z3 d p `using` runner U.satWith

-- | Entry point for problems that return IO or to benchmark IO results
runIOWith :: NFData a => (a -> Benchmarkable) -> String -> a -> Runner
runIOWith f d = RBenchmark . bench d . f

-- | Benchmark an IO result of sbv, this could be codegen, return models, etc..
-- See @runIOWith@ for a version which allows the consumer to select the
-- Benchmarkable injection function
runIO :: NFData a => String -> IO a -> Runner
runIO d = RBenchmark . bench d . nfIO . silence

-- | Benchmark an pure result
runPure :: NFData a => String -> (a -> b) -> a -> Runner
runPure d = (RBenchmark . bench d) .: whnf
  where (.:) = (.).(.)

-- | create a runner group. Useful for benchmarks that need to run several
-- benchmarks. See 'BenchSuite.Puzzles.NQueens' for an example.
rGroup :: [Runner] -> Runner
rGroup = RunnerGroup

-- | Orphaned instances just for benchmarking
instance NFData U.AllSatResult where
  rnf (U.AllSatResult (a, b, c, results)) =
    rnf a `seq` rnf b `seq` rnf c `seq` rwhnf results

-- | Unwrap the existential type to make gauge happy
instance NFData BenchResult where rnf (BenchResult a) = rnf a
