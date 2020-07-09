-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.DogCatMouse
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.DogCatMouse
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.DogCatMouse(benchmarks) where

import Utils.SBVBenchFramework
import BenchSuite.Bench.Bench as S


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup [ S.run "DogCatMouse" p `using` runner allSatWith ]
  where p = do [dog, cat, mouse] <- sIntegers ["dog", "cat", "mouse"]
               solve [ dog   .>= 1                                   -- at least one dog
                     , cat   .>= 1                                   -- at least one cat
                     , mouse .>= 1                                   -- at least one mouse
                     , dog + cat + mouse .== 100                     -- buy precisely 100 animals
                     , 1500 * dog + 100 * cat + 25 * mouse .== 10000 -- spend exactly 100 dollars (use cents since we don't have fractions)
                     ]
