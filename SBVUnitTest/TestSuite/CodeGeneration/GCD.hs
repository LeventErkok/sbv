-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CodeGeneration.GCD
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CodeGeneration.GCD
-----------------------------------------------------------------------------

module TestSuite.CodeGeneration.GCD(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.GCD

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "gcd" ~: gcdC `goldCheck` "gcd.gold"
 ]
 where gcdC = compileToC' "sgcd" $ do
                cgSetDriverValues [55,154]
                x <- cgInput "x"
                y <- cgInput "y"
                cgReturn $ sgcd x y
