-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.SquashReals
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the "squash" reals feature
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.SquashReals(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Reals.Squash"
    [ goldenVsStringShow "squashReals1" $ sat                            (\x -> x .>= 0 .&& x*x .== (59::SReal))
    , goldenVsStringShow "squashReals2" $ sat                            (\x -> x .>= 0 .&& x*x .== (16::SReal))
    , goldenVsStringShow "squashReals3" $ satWith z3{printRealPrec = 35} (\x -> x .>= 0 .&& x*x .== (59::SReal))
    , goldenVsStringShow "squashReals4" $ satWith z3{printRealPrec = 35} (\x -> x .>= 0 .&& x*x .== (16::SReal))
    ]
