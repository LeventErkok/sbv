-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.BitPrecise.BrokenSearch
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.BitPrecise.BrokenSearch
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.BitPrecise.BrokenSearch(benchmarks) where

import Documentation.SBV.Examples.BitPrecise.BrokenSearch
import BenchSuite.Bench.Bench as B

import Data.SBV (proveWith,sInt32,(.>=),(.<=),(.==),sFromIntegral,SInt64,sDiv,constrain)

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ B.run  "Arith.MidPointFixed"  (checkCorrect midPointFixed)        `using` runner Data.SBV.proveWith
  , B.run  "Arith-Overflow"       (checkCorrect midPointAlternative)  `using` runner Data.SBV.proveWith
  ]

  where checkCorrect f = do low  <- sInt32 "low"
                            high <- sInt32 "high"

                            constrain $ low .>= 0
                            constrain $ low .<= high

                            let low', high' :: SInt64
                                low'  = sFromIntegral low
                                high' = sFromIntegral high
                                mid'  = (low' + high') `sDiv` 2

                                mid   = f low high

                            return $ sFromIntegral mid .== mid'
