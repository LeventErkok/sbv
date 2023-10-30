-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.IteTest
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test various incarnations of laziness in ite
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.IteTest(tests)  where

import Utils.SBVTestFramework

chk1 :: (SBool -> SBool -> SBool -> SBool) -> SWord8 -> SBool
chk1 cond x = cond (x .== x) sTrue undefined

chk2 :: (SBool -> [SBool] -> [SBool] -> [SBool]) -> SWord8 -> SBool
chk2 cond x = case cond (x .== x) [sTrue] [undefined] of
                [v] -> v
                _   -> error "chk2: Impossible happened in call to cond!"

chk3 :: (SBool -> (SBool, SBool) -> (SBool, SBool)  -> (SBool, SBool)) -> SWord8 -> SBool
chk3 cond x = fst (cond (x .== x) (sTrue, undefined::SBool) (undefined, undefined))

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Ite"
    [ testCase "iteTest1" (chk1 ite 0 `showsAs` "True")
    , testCase "iteTest2" (chk2 ite 0 `showsAs` "True")
    , testCase "iteTest3" (chk3 ite 0 `showsAs` "True")
    , testCase "iteTest4" (assertIsThm (chk1 iteLazy))
    , testCase "iteTest5" (assertIsThm (chk2 iteLazy))
    , testCase "iteTest6" (assertIsThm (chk3 iteLazy))
    ]
