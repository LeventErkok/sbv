-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Existentials.Diophantine
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Existentials.Diophantine
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.Existentials.Diophantine(benchmarks) where

import Documentation.SBV.Examples.Existentials.Diophantine
import Control.DeepSeq

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks =  rGroup
              [ runIO "Test"    test
              , runIO "Sailors" sailors
              ]



instance NFData Solution where rnf x = seq x ()
