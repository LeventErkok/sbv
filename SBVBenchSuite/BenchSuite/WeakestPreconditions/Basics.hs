-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.Basics
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.Basics
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE NamedFieldPuns #-}

module BenchSuite.WeakestPreconditions.Basics(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.Basics
import Data.SBV
import Data.SBV.Tools.WeakestPreconditions

import Control.DeepSeq
import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()

instance NFData a => NFData (IncS a)


benchmarks :: Runner
benchmarks = rGroup
  [ runIO "Correctness.Basics skip"        $ correctness Skip Skip
  , runIO "Correctness.Basics y+1"         $ correctness Skip $ Assign $ \st@IncS{y} -> st{y = y+1}
  , runIO "Correctness.Basics x>0"         $ correctness (assert "x > 0" (\IncS{x} -> x .> 0)) Skip
  , runIO "Correctness.Basics x>-5"        $ correctness (assert "x > -5" (\IncS{x} -> x .> -5)) Skip
  , runIO "Correctness.Basics y is even"   $ correctness Skip (assert "y is even" (\IncS{y} -> y `sMod` 2 .== 0))
  , runIO "Correctness.Basics y > x"       $ correctness Skip (assert "y > x" (\IncS{x, y} -> y .> x))
  , runIO "Correctness.Basics skip-assign" $ correctness Skip (Assign $ \st -> st{x = 10, y = 11})
  ]
