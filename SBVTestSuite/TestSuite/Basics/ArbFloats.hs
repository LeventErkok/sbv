-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ArbFloats
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Basic arbitrary float checks
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.ArbFloats(tests) where

import Utils.SBVTestFramework

-- # of inhabitants is 2^sb(2^eb - 1) + 3
count :: Integer -> Integer -> Integer
count eb sb = 2^sb * (2^eb - 1) + 3

tests :: TestTree
tests = testGroup "Basics.ArbFloats"
  [ testCase "FP_2_2" (assert $ (== fromIntegral (count 2 2)) <$> numberOfModels (const sTrue :: SFloatingPoint 2 2 -> SBool))
  , testCase "FP_2_3" (assert $ (== fromIntegral (count 2 3)) <$> numberOfModels (const sTrue :: SFloatingPoint 2 3 -> SBool))
  , testCase "FP_2_4" (assert $ (== fromIntegral (count 2 4)) <$> numberOfModels (const sTrue :: SFloatingPoint 2 4 -> SBool))

  , testCase "FP_3_2" (assert $ (== fromIntegral (count 3 2)) <$> numberOfModels (const sTrue :: SFloatingPoint 3 2 -> SBool))
  , testCase "FP_3_3" (assert $ (== fromIntegral (count 3 3)) <$> numberOfModels (const sTrue :: SFloatingPoint 3 3 -> SBool))
  , testCase "FP_3_4" (assert $ (== fromIntegral (count 3 4)) <$> numberOfModels (const sTrue :: SFloatingPoint 3 4 -> SBool))

  , testCase "FP_4_2" (assert $ (== fromIntegral (count 4 2)) <$> numberOfModels (const sTrue :: SFloatingPoint 4 2 -> SBool))
  , testCase "FP_4_3" (assert $ (== fromIntegral (count 4 3)) <$> numberOfModels (const sTrue :: SFloatingPoint 4 3 -> SBool))
  , testCase "FP_4_4" (assert $ (== fromIntegral (count 4 4)) <$> numberOfModels (const sTrue :: SFloatingPoint 4 4 -> SBool))

  , goldenVsStringShow "arbFp_opt_1" (optimize Lexicographic $ \x -> do {constrain (fpIsPoint x);  maximize "x" (x::SFPHalf)})
  ]
