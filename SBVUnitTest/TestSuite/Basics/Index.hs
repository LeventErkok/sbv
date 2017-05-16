-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.Index
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Basics.Index
-----------------------------------------------------------------------------

module TestSuite.Basics.Index(tests) where

import Examples.Basics.Index (test1, test2, test3)
import SBVTest

tests :: TestTree
tests =
  testGroup "Basics.Index"
    (zipWith
      mkTest
      [f x | f <- [test1, test2, test3], x <- [0..13]]
      [(0::Int)..])

mkTest :: IO Bool -> Int -> TestTree
mkTest tst i =
  testCase ("index-" ++ show i)
    (assert tst)