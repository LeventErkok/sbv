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
import BenchSuite.Bench.Bench as S

import Data.Maybe (fromMaybe)


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
    [ runIO ("sudoku" ++ show n) (checkPuzzle s)
    | (n, s) <- zip [(0::Int)..] [puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6] ]


checkPuzzle :: Puzzle -> IO Bool
checkPuzzle p = do final <- fillBoard p
                   let vld = valid (map (map literal) final)
                   pure $ fromMaybe False (unliteral vld)
