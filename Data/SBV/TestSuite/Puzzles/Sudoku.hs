-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Puzzles.Sudoku
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.Sudoku
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Puzzles.Sudoku(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.Sudoku

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
  "sudoku " ++ show n ~: assert (checkPuzzle s)
     | (n, s) <- zip [(0::Int)..] [puzzle0, puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6]
 ]
 where checkPuzzle (i, f) = isSatisfiable $ mapM (const free_) [1..i] >>= output . valid . f
