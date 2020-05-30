-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Queries.Enums
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Queries.Enums
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.Queries.Enums(benchmarks) where

import Documentation.SBV.Examples.Queries.Enums

import Control.DeepSeq
import BenchSuite.Bench.Bench

-- | orphaned instance for benchmarks
instance NFData Day where rnf x = seq x ()

benchmarks :: Runner
benchmarks = rGroup [ runIO "Enums.findDays" findDays
                    ]
