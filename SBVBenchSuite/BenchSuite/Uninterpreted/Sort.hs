-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Uninterpreted.Sort
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Uninterpreted.Sort
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Uninterpreted.Sort(benchmarks) where

import Documentation.SBV.Examples.Uninterpreted.Sort
import Data.SBV

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks = rGroup
  [ run "t1" _t1 `using` runner satWith
  , run "r2" _t1 `using` runner satWith
  ]
  where _t1 = do x <- free "x"
                 return $ f x ./= x

        _t2 = do x <- free "x"
                 addAxiom "Q" ["(assert (forall ((x Q) (y Q)) (= x y)))"]
                 return $ f x ./= x
