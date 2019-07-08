-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.BitPrecise.BitTricks
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.BitPrecise.BitTricks
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.BitPrecise.BitTricks(tests) where

import Documentation.SBV.Examples.BitPrecise.BitTricks

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "BitPrecise.BitTricks"
    [ testCase "fast min"              $ assertIsThm fastMinCorrect
    , testCase "fast max"              $ assertIsThm fastMaxCorrect
    , testCase "opposite signs"        $ assertIsThm oppositeSignsCorrect
    , testCase "conditional set clear" $ assertIsThm conditionalSetClearCorrect
    , testCase "power of two"          $ assertIsThm powerOfTwoCorrect
    ]
