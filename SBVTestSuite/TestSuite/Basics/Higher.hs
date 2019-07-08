-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Higher
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.Basics.Higher
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Higher(tests) where

import Utils.SBVTestFramework

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

type B = SWord8

f11 :: B -> B
f11 x = x

f12 :: B -> (B, B)
f12 x = (x, x)

f21 :: (B, B) -> B
f21 (x, y) = x + y

f22 :: (B, B) -> (B, B)
f22 (x, y) = (x, y)

f31 :: B -> B -> B
f31 x y = x + y

f32 :: B -> B -> (B, B)
f32 x y = (x, y)

f33 :: B -> B -> B -> (B, B, B)
f33 x y z = (x, y, z)
