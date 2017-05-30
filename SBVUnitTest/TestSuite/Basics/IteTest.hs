-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.IteTest
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test various incarnations of ite/iteLazy/sBranch
-----------------------------------------------------------------------------

module TestSuite.Basics.IteTest(tests)  where

import Data.SBV

import SBVTest

chk1 :: (SBool -> SBool -> SBool -> SBool) -> SWord8 -> SBool
chk1 cond x = cond (x .== x) true undefined

chk2 :: (SBool -> [SBool] -> [SBool] -> [SBool]) -> SWord8 -> SBool
chk2 cond x = head (cond (x .== x) [true] [undefined])

chk3 :: (SBool -> (SBool, SBool) -> (SBool, SBool)  -> (SBool, SBool)) -> SWord8 -> SBool
chk3 cond x = fst (cond (x .== x) (true, undefined::SBool) (undefined, undefined))

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Ite"
    [ goldenVsStringShow "ite-1" "iteTest1.gold" (rs (chk1 ite))
    , goldenVsStringShow "ite-2" "iteTest2.gold" (rs (chk2 ite))
    , goldenVsStringShow "ite-3" "iteTest3.gold" (rs (chk3 ite))
    , testCase "ite-4" (assertIsThm (chk1 iteLazy))
    , testCase "ite-5" (assertIsThm (chk2 iteLazy))
    , testCase "ite-6" (assertIsThm (chk3 iteLazy))
    ]
 where rs f = runSAT $ forAll ["x"] f
