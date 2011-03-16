-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CodeGeneration.Fibonacci
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CodeGeneration.Fibonacci
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CodeGeneration.Fibonacci(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.Fibonacci

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "fib1" ~: compileToC' [12] True "fib1" ["n"] (fib1 64) `goldCheck` "fib1.gold"
 , "fib2" ~: compileToC' [20] True "fib2" ["n"] (fib2 64) `goldCheck` "fib2.gold"
 ]
