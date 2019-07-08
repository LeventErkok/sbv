-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.QRem
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.Basics.QRem
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.QRem(tests) where

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Basics.QRem"
    [ testCase "qremW8" (assertIsThm (qrem :: SWord8   -> SWord8   -> SBool))
    , testCase "qremI8" (assertIsThm (qrem :: SInt8    -> SInt8    -> SBool))
    , testCase "qremI"  (assertIsThm (qrem :: SInteger -> SInteger -> SBool))
    ]

-- check: if (a, b) = x `quotRem` y then x = y*a + b
-- same is also true for divMod
-- being careful about y = 0. When divisor is 0, then quotient is
-- defined to be 0 and the remainder is the numerator
qrem :: (Num a, EqSymbolic a, SDivisible a) => a -> a -> SBool
qrem x y = ite (y .== 0)
               ((0, x) .== (q, r) .&& (0, x) .== (d, m))
               (x .== y * q + r .&& x .== y * d + m)
  where (q, r) = x `sQuotRem` y
        (d, m) = x `sDivMod` y
