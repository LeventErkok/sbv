-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.SoftConstrain
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.SoftConstrain
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Misc.SoftConstrain(benchmarks) where

import Data.SBV
import BenchSuite.Bench.Bench


-- benchmark suite
benchmarks :: Runner
benchmarks =  rGroup [ run "SoftConstrain" softC ]
  where softC = do x <- sString "x"
                   y <- sString "y"

                   constrain $ x .== "x-must-really-be-hello"
                   constrain $ y ./= "y-can-be-anything-but-hello"

                   -- Now add soft-constraints to indicate our preference
                   -- for what these variables should be:
                   softConstrain $ x .== "default-x-value"
                   softConstrain $ y .== "default-y-value"

                   return sTrue
