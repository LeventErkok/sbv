-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.NoDiv0
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.NoDiv0
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.Misc.NoDiv0(benchmarks) where

import Documentation.SBV.Examples.Misc.NoDiv0

import Data.SBV
import Control.DeepSeq
import BenchSuite.Bench.Bench


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ runIO "test.1" test1
             , runIO "test.2" test2
             ]

instance NFData SafeResult where rnf x = seq x ()
