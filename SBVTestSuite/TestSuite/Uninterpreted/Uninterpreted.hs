-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Uninterpreted.Uninterpreted
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.Uninterpreted(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.Uninterpreted"
    [ testCase "uninterpreted-0" (assertIsThm p0)
    , testCase "uninterpreted-1" (assertIsThm p1)
    , testCase "uninterpreted-2" (assertIsntThm p2)
    ]

f :: SInt8 -> SWord32
f = uninterpret "f"

g :: SInt8 -> SWord16 -> SWord32
g = uninterpret "g"

p0 :: SInt8 -> SInt8 -> SBool
p0 x y   = x .== y .=> f x .== f y      -- OK

p1 :: SInt8 -> SWord16 -> SWord16 -> SBool
p1 x y z = y .== z .=> g x y .== g x z  -- OK

p2 :: SInt8 -> SWord16 -> SWord16 -> SBool
p2 x y z = y .== z .=> g x y .== f x    -- Not true
