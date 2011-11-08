-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Puzzles.NQueens
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.NQueens
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Puzzles.NQueens(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.NQueens

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   -- number of *distinct* solutions is given in http://en.wikipedia.org/wiki/Eight_queens_puzzle
   "nQueens 1" ~: assert $ (==  1) `fmap` numberOfModels (mkQueens 1)
 , "nQueens 2" ~: assert $ (==  0) `fmap` numberOfModels (mkQueens 2)
 , "nQueens 3" ~: assert $ (==  0) `fmap` numberOfModels (mkQueens 3)
 , "nQueens 4" ~: assert $ (==  2) `fmap` numberOfModels (mkQueens 4)
 , "nQueens 5" ~: assert $ (== 10) `fmap` numberOfModels (mkQueens 5)
 , "nQueens 6" ~: assert $ (==  4) `fmap` numberOfModels (mkQueens 6)
 , "nQueens 7" ~: assert $ (== 40) `fmap` numberOfModels (mkQueens 7)
 , "nQueens 8" ~: assert $ (== 92) `fmap` numberOfModels (mkQueens 8)
 ]
 where mkQueens n = isValid n `fmap` mkExistVars n
