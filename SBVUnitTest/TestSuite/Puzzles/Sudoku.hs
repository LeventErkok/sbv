-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Sudoku
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Puzzles.Sudoku
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Sudoku(testSuite) where

import Data.SBV
import Data.SBV.Examples.Puzzles.Sudoku

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
  "sudoku " ++ show n ~: assert (checkPuzzle s)
     | (n, s) <- zip [(0::Int)..] [puzzle0, puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6]
 ]
 where checkPuzzle (i, f) = isSat $ (valid . f) `fmap` mkExistVars i
