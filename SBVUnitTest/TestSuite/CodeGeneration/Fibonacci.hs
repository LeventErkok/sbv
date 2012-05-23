-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CodeGeneration.Fibonacci
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.CodeGeneration.Fibonacci
-----------------------------------------------------------------------------

module TestSuite.CodeGeneration.Fibonacci(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.Fibonacci

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "fib1" ~: tst [12] "fib1" (fib1 64) `goldCheck` "fib1.gold"
 , "fib2" ~: tst [20] "fib2" (fib2 64) `goldCheck` "fib2.gold"
 ]
 where tst vs nm f = compileToC' nm $ do cgPerformRTCs True
                                         cgSetDriverValues vs
                                         n <- cgInput "n"
                                         cgReturn $ f n
