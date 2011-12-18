-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Basics.Index
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Basics.Index
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Basics.Index(testSuite) where

import Data.SBV.Internals
import Data.SBV.Examples.Basics.Index

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test $ zipWith tst [f x | f <- [test1, test2, test3], x <- [0..13]] [(0::Int)..]
  where tst t i = "index-" ++ show i ~: t `ioShowsAs` "True"
