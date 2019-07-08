-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CRC.Parity
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.CRC.Parity
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CRC.Parity(tests) where

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "CRC.Parity"
    [ testCase "parity" (assertIsThm parityOK)
    ]

parity :: SWord64 -> SBool
parity x = sNot (isOdd cnt)
  where cnt :: SWord8
        cnt = sum $ map oneIf $ blastLE x

isOdd :: SWord8 -> SBool
isOdd = lsb

-- Example suggested by Lee Pike
-- If x and y differ in odd-number of bits, then their parities are flipped
parityOK :: SWord64 -> SWord64 -> SBool
parityOK x y = isOdd cnt .=> px .== sNot py
  where cnt = sum $ map oneIf $ zipWith (./=) (blastLE x) (blastLE y)
        px  = parity x
        py  = parity y
