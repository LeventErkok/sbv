-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.Higher
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.Basics.Higher
-----------------------------------------------------------------------------

module TestSuite.Basics.Higher(testSuite) where

import Data.SBV

import Examples.Basics.Higher
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "higher-1"  ~: (f11 === f11)   `goldCheck` "higher-1.gold"
 , "higher-2"  ~: (f12 === f12)   `goldCheck` "higher-2.gold"
 , "higher-3"  ~: (f21 === f21)   `goldCheck` "higher-3.gold"
 , "higher-4"  ~: (f22 === f22)   `goldCheck` "higher-4.gold"
 , "higher-5"  ~: (f31 === f31)   `goldCheck` "higher-5.gold"
 , "higher-6"  ~: (f32 === f32)   `goldCheck` "higher-6.gold"
 , "higher-7"  ~: (f33 === f33)   `goldCheck` "higher-7.gold"
 , "higher-8"  ~: double          `goldCheck` "higher-8.gold"
 , "higher-9"  ~: onlyFailsFor128 `goldCheck` "higher-9.gold"
 ]
 where double          = (2*) === (\x -> x+(x::SWord8))
       onlyFailsFor128 = (2*) === (\x -> ite (x .== 128) 5 (x+(x::SWord8)))

