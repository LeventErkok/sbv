-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.Coins
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.Coins
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.Coins(benchmarks) where

import Documentation.SBV.Examples.Puzzles.Coins

import Utils.SBVBenchFramework
import BenchSuite.Bench.Bench as S


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup [ S.run "Coins" coinsPgm ]
  where coinsPgm = do cs <- mapM mkCoin [1..6]
                      mapM_ constrain [c s | s <- combinations cs, length s >= 2, c <- [c1, c2, c3, c4, c5, c6]]
                      constrain $ sAnd $ zipWith (.>=) cs (drop 1 cs)
                      -- normally we would call output here, but returning
                      -- several outputs from a symbolic computation doesn't
                      -- play nice with either the transcript generation or the benchmarking apparently

                      -- output $ sum cs .== 115

                      return $ sum cs .== 115
