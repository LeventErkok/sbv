-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Basics.UnsafeFunctionEquality
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Basics.UnsafeFunctionEquality
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Basics.UnsafeFunctionEquality(testSuite) where

import Data.SBV.Internals
import Data.SBV.Examples.Basics.UnsafeFunctionEquality

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "functionEq-1" ~: assert       $ f11 == f11
 , "functionEq-2" ~: assert       $ f12 == f12
 , "functionEq-3" ~: assert       $ f22 == f22
 , "functionEq-4" ~: assert       $ f31 == f31
 , "functionEq-5" ~: assert       $ f32 == f32
 , "functionEq-6" ~: assert       $ f33 == f33
 , "functionEq-7" ~: assert . not $ f11 /= f11
 ]
