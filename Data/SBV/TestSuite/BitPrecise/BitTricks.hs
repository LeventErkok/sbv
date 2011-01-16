-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.BitPrecise.BitTricks
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.BitPrecise.BitTricks
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.BitPrecise.BitTricks(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.BitPrecise.BitTricks

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "fast min"              ~: assert =<< isTheorem fastMinCorrect
 , "fast max"              ~: assert =<< isTheorem fastMaxCorrect
 , "opposite signs"        ~: assert =<< isTheorem oppositeSignsCorrect
 , "conditional set clear" ~: assert =<< isTheorem conditionalSetClearCorrect
 , "power of two"          ~: assert =<< isTheorem powerOfTwoCorrect
 ]
