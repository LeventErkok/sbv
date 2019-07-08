-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Crypto.RC4
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Crypto.RC4
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Crypto.RC4(tests) where

import Data.SBV.Tools.STree
import Documentation.SBV.Examples.Crypto.RC4

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Crypto.RC4"
    [ testCase "rc4swap" (assertIsThm readWrite)
    ]

readWrite :: SBV Word8 -> SBV Word8 -> SBV Bool
readWrite i j = readSTree (writeSTree initS i j) i .== j
