-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.LadyAndTigers
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.LadyAndTigers
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.LadyAndTigers(benchmarks) where


import Utils.SBVBenchFramework
import BenchSuite.Bench.Bench as S


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup [ S.run "LadyAndTigers" p `using` runner allSatWith ]
  where p = do

          -- One boolean for each of the correctness of the signs
          [sign1, sign2, sign3] <- mapM sBool ["sign1", "sign2", "sign3"]

          -- One boolean for each of the presence of the tigers
          [tiger1, tiger2, tiger3] <- mapM sBool ["tiger1", "tiger2", "tiger3"]

          -- Room 1 sign: A Tiger is in this room
          constrain $ sign1 .<=> tiger1

          -- Room 2 sign: A Lady is in this room
          constrain $ sign2 .<=> sNot tiger2

          -- Room 3 sign: A Tiger is in room 2
          constrain $ sign3 .<=> tiger2

          -- At most one sign is true
          constrain $ [sign1, sign2, sign3] `pbAtMost` 1

          -- There are precisely two tigers
          constrain $ [tiger1, tiger2, tiger3] `pbExactly` 2
