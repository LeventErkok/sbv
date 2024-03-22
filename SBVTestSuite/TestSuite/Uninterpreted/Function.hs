-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Uninterpreted.Function
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testsuite for Documentation.SBV.Examples.Uninterpreted.Function
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Uninterpreted.Function(tests) where

import Documentation.SBV.Examples.Uninterpreted.Function

import Utils.SBVTestFramework

data A1
mkUninterpretedSort ''A1

data A2
mkUninterpretedSort ''A2

data A3
mkUninterpretedSort ''A3

data A4
mkUninterpretedSort ''A4

data A5
mkUninterpretedSort ''A5

data A6
mkUninterpretedSort ''A6

data A7
mkUninterpretedSort ''A7

data A8
mkUninterpretedSort ''A8

data A9
mkUninterpretedSort ''A9

data A10
mkUninterpretedSort ''A10

data A11
mkUninterpretedSort ''A11

data A12
mkUninterpretedSort ''A12


f1 :: SA1 -> SBool
f1 = uninterpret "f1"

f2 :: SA1 -> SA2 -> SBool
f2 = uninterpret "f2"

f3 :: SA1 -> SA2 -> SA3 -> SBool
f3 = uninterpret "f3"

f4 :: SA1 -> SA2 -> SA3 -> SA4 -> SBool
f4 = uninterpret "f4"

f5 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SBool
f5 = uninterpret "f5"

f6 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SBool
f6 = uninterpret "f6"

f7 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SBool
f7 = uninterpret "f7"

f8 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SBool
f8 = uninterpret "f8"

f9 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SBool
f9 = uninterpret "f9"

f10 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SA10 -> SBool
f10 = uninterpret "f10"

f11 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SA10 -> SA11 -> SBool
f11 = uninterpret "f11"

f12 :: SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SA10 -> SA11 -> SA12 -> SBool
f12 = uninterpret "f12"

thm1 :: SA1 -> SA1 -> SBool
thm1 x a1 =
  x .== a1
  .=> f1 x .== f1 a1

thm2 :: SA1 -> SA1 -> SA2 -> SBool
thm2 x a1 a2 =
  x .== a1
  .=> f2 x a2 .== f2 a1 a2

thm3 :: SA1 -> SA1 -> SA2 -> SA3 -> SBool
thm3 x a1 a2 a3 =
  x .== a1
  .=> f3 x a2 a3 .== f3 a1 a2 a3

thm4 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SBool
thm4 x a1 a2 a3 a4 =
  x .== a1
  .=> f4 x a2 a3 a4 .== f4 a1 a2 a3 a4

thm5 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SBool
thm5 x a1 a2 a3 a4 a5 =
  x .== a1
  .=> f5 x a2 a3 a4 a5 .== f5 a1 a2 a3 a4 a5

thm6 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SBool
thm6 x a1 a2 a3 a4 a5 a6 =
  x .== a1
  .=> f6 x a2 a3 a4 a5 a6 .== f6 a1 a2 a3 a4 a5 a6

thm7 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SBool
thm7 x a1 a2 a3 a4 a5 a6 a7 =
  x .== a1
  .=> f7 x a2 a3 a4 a5 a6 a7 .== f7 a1 a2 a3 a4 a5 a6 a7

thm8 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SBool
thm8 x a1 a2 a3 a4 a5 a6 a7 a8 =
  x .== a1
  .=> f8 x a2 a3 a4 a5 a6 a7 a8 .== f8 a1 a2 a3 a4 a5 a6 a7 a8

thm9 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SBool
thm9 x a1 a2 a3 a4 a5 a6 a7 a8 a9 =
  x .== a1
  .=> f9 x a2 a3 a4 a5 a6 a7 a8 a9 .== f9 a1 a2 a3 a4 a5 a6 a7 a8 a9

thm10 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SA10 -> SBool
thm10 x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =
  x .== a1
  .=> f10 x a2 a3 a4 a5 a6 a7 a8 a9 a10 .== f10 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10

thm11 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SA10 -> SA11 -> SBool
thm11 x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 =
  x .== a1
  .=> f11 x a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 .== f11 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11

thm12 :: SA1 -> SA1 -> SA2 -> SA3 -> SA4 -> SA5 -> SA6 -> SA7 -> SA8 -> SA9 -> SA10 -> SA11 -> SA12 -> SBool
thm12 x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =
  x .== a1
  .=> f12 x a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 .== f12 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12

tests :: TestTree
tests =
  testGroup "Uninterpreted.Function"
  [ testCase "aufunc-0" (assertIsThm thmGood)
  , testCase "aufunc-1" (assertIsThm thm1)
  , testCase "aufunc-2" (assertIsThm thm2)
  , testCase "aufunc-3" (assertIsThm thm3)
  , testCase "aufunc-4" (assertIsThm thm4)
  , testCase "aufunc-5" (assertIsThm thm5)
  , testCase "aufunc-6" (assertIsThm thm6)
  , testCase "aufunc-7" (assertIsThm thm7)
  , testCase "aufunc-8" (assertIsThm thm8)
  , testCase "aufunc-9" (assertIsThm thm9)
  , testCase "aufunc-10" (assertIsThm thm10)
  , testCase "aufunc-11" (assertIsThm thm11)
  , testCase "aufunc-12" (assertIsThm thm12)
  ]
