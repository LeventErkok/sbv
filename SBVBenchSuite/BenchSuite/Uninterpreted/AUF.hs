-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Uninterpreted.AUF
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchSuite.Uninterpreted.AUF(benchmarks) where

import Documentation.SBV.Examples.Uninterpreted.AUF
import Data.SBV

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks = rGroup
  [ run "SArray" array `using` runner proveWith
  ]
  where array = do x <- free "x"
                   y <- free "y"
                   a :: SArray Word32 Word32 <- newArray_ Nothing
                   return $ thm x y a
