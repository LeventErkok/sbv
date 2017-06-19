-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.Higher
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Basics.Higher
-----------------------------------------------------------------------------

module TestSuite.Basics.Higher(tests) where

import Data.SBV

import Examples.Basics.Higher
import SBVTest

tests :: TestTree
tests =
  testGroup "Basics.Higher"
    [ goldenVsStringShow "higher-1" (f11 === f11)
    , goldenVsStringShow "higher-2" (f12 === f12)
    , goldenVsStringShow "higher-3" (f21 === f21)
    , goldenVsStringShow "higher-4" (f22 === f22)
    , goldenVsStringShow "higher-5" (f31 === f31)
    , goldenVsStringShow "higher-6" (f32 === f32)
    , goldenVsStringShow "higher-7" (f33 === f33)
    , goldenVsStringShow "higher-8" double
    , goldenVsStringShow "higher-9" onlyFailsFor128
    ]
 where double          = (2*) === (\x -> x+(x::SWord8))
       onlyFailsFor128 = (2*) === (\x -> ite (x .== 128) 5 (x+(x::SWord8)))
