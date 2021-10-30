-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.BitPrecise.MultMask
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.BitPrecise.MultMask
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.BitPrecise.MultMask(benchmarks) where

import BenchSuite.Bench.Bench as B

import Data.SBV

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ B.runWith conf "MultMask" find
  ]
  where find = do mask <- sbvExists "mask"
                  mult <- sbvExists "mult"
                  inp  <- sbvForall "inp"
                  let res = (mask .&. inp) * (mult :: SWord64)
                  solve [inp `sExtractBits` [7, 15 .. 63] .== res `sExtractBits` [56 .. 63]]
        conf = z3{printBase=16, satCmd = "(check-sat-using (and-then simplify smtfd))"}
