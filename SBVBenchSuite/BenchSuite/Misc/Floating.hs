-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.Floating
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.Floating
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE ScopedTypeVariables #-}

module BenchSuite.Misc.Floating(benchmarks) where

import Documentation.SBV.Examples.Misc.Floating

import BenchSuite.Bench.Bench
import Utils.SBVBenchFramework


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ run "notAssoc"        (assocPlus (0/0)) `using` runner proveWith
             , run "AssocPlusReg"    _assocPlusRegular `using` runner proveWith
             , run "NonZeroAddition" _nonZeroAddition  `using` runner proveWith
             , run "MultInverse"     _multInverse      `using` runner proveWith
             , run "RoundingAdd"     _roundingAdd
             ]
  where _assocPlusRegular = do [x, y, z] <- sFloats ["x", "y", "z"]
                               let lhs = x+(y+z)
                                   rhs = (x+y)+z
                               -- make sure we do not overflow at the intermediate points
                               constrain $ fpIsPoint lhs
                               constrain $ fpIsPoint rhs
                               return $ lhs .== rhs

        _nonZeroAddition  = do [a, b] <- sFloats ["a", "b"]
                               constrain $ fpIsPoint a
                               constrain $ fpIsPoint b
                               constrain $ a + b .== a
                               return $ b .== 0

        _multInverse      = do a <- sFloat "a"
                               constrain $ fpIsPoint a
                               constrain $ fpIsPoint (1/a)
                               return $ a * (1/a) .== 1

        _roundingAdd      = do m :: SRoundingMode <- free "rm"
                               constrain $ m ./= literal RoundNearestTiesToEven
                               x <- sFloat "x"
                               y <- sFloat "y"
                               let lhs = fpAdd m x y
                               let rhs = x + y
                               constrain $ fpIsPoint lhs
                               constrain $ fpIsPoint rhs
                               return $ lhs ./= rhs
