-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.Sudoku
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.Sudoku
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.Sudoku(benchmarks) where

import Documentation.SBV.Examples.Puzzles.Sudoku

import Utils.SBVBenchFramework
import BenchSuite.Overhead.SBVOverhead


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
    [ runner ("sudoku " ++ show n) (checkPuzzle s) `using` setRunner allSatWith
       | (n, s) <-
           zip
             [(0::Int)..]
             [puzzle0, puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6] ]


checkPuzzle :: Puzzle -> Symbolic SBool
checkPuzzle (i, f) = (valid . f) `fmap` mkExistVars i
