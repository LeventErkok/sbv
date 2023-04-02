-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.Sudoku
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.Sudoku
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.Sudoku(tests) where

import Documentation.SBV.Examples.Puzzles.Sudoku

import Data.Maybe (fromMaybe)
import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Puzzles.Sudoku"
    [ testCase ("sudoku " ++ show n) (assert (checkPuzzle s))
       | (n, s) <- zip [(0::Int)..] [puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6] ]

checkPuzzle :: Puzzle -> IO Bool
checkPuzzle p = do final <- fillBoard p
                   let vld = valid (map (map literal) final)
                   pure $ fromMaybe False (unliteral vld)
