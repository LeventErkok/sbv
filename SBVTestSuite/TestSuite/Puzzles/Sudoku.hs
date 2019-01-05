-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.Sudoku
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.Sudoku
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Sudoku(tests) where

import Documentation.SBV.Examples.Puzzles.Sudoku

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Puzzles.Sudoku"
    [ testCase ("sudoku " ++ show n) (assert (checkPuzzle s))
       | (n, s) <-
           zip
             [(0::Int)..]
             [puzzle0, puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6] ]

checkPuzzle :: Puzzle -> IO Bool
checkPuzzle (i, f) = isSatisfiable $ (valid . f) `fmap` mkExistVars i
