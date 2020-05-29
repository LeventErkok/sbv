-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Optimization.Instance
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Helper file to provide common orphaned instances for Optimization benchmarks
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.Optimization.Instances where

import Data.SBV

import Control.DeepSeq


-- | orphaned instance for benchmarks
instance NFData OptimizeResult where rnf x = seq x ()
