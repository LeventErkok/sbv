-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.BitPrecise.BitTricks
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.BitPrecise.BitTricks
-----------------------------------------------------------------------------

module TestSuite.BitPrecise.BitTricks(testSuite) where

import Data.SBV.Examples.BitPrecise.BitTricks

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "fast min"              ~: assert =<< isThm fastMinCorrect
 , "fast max"              ~: assert =<< isThm fastMaxCorrect
 , "opposite signs"        ~: assert =<< isThm oppositeSignsCorrect
 , "conditional set clear" ~: assert =<< isThm conditionalSetClearCorrect
 , "power of two"          ~: assert =<< isThm powerOfTwoCorrect
 ]
