-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Uninterpreted.Deduce
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Uninterpreted.Deduce
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchSuite.Uninterpreted.Deduce(benchmarks) where

import Documentation.SBV.Examples.Uninterpreted.Deduce
import Data.SBV

import Prelude hiding (not, or, and)
import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks = rGroup
  [ run "test" t `using` runner proveWith
  ]
  where t = do addAxiom "OR distributes over AND" ax1
               addAxiom "de Morgan"               ax2
               addAxiom "double negation"         ax3
               p <- free "p"
               q <- free "q"
               r <- free "r"
               return $ not (p `or` (q `and` r))
                 .== (not p `and` not q) `or` (not p `and` not r)
