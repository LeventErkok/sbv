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

module TestSuite.Basics.Index(testSuite) where

import Examples.Basics.Index
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test $ zipWith tst [f x | f <- [test1, test2, test3], x <- [0..13]] [(0::Int)..]
  where tst t i = "index-" ++ show i ~: t `ioShowsAs` "True"
