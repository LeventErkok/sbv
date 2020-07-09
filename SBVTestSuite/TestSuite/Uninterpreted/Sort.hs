-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Uninterpreted.Sort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for uninterpreted sorts
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Uninterpreted.Sort(tests) where

import Utils.SBVTestFramework

data L
mkUninterpretedSort ''L

tests :: TestTree
tests =
  testGroup "Uninterpreted.Sort"
    [ testCase "unint-sort"
        (assert . (==4) . length . (extractModels :: AllSatResult -> [L]) =<< allSat p0)
    ]

len :: SL -> SInteger
len = uninterpret "len"

p0 :: Symbolic SBool
p0 = do
    [l, l0, l1] <- symbolics ["l", "l0", "l1"]
    constrain $ len l0 .== 0
    constrain $ len l1 .== 1
    x :: SInteger <- symbolic "x"
    constrain $ x .== 0 .|| x.== 1
    return $ l .== l0 .|| l .== l1
