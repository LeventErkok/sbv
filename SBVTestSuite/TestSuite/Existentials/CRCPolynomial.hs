-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Existentials.CRCPolynomial
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Existentials.CRCPolynomial
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Existentials.CRCPolynomial(tests) where

import Documentation.SBV.Examples.Existentials.CRCPolynomial

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Existentials.CRCPolynomial" [
    goldenVsStringShow "crcPolyExist" (runSAT pgm)
  , testCase "crcPolyGood" (assertIsSat pgm)
 ]

pgm :: Predicate
pgm = do p <- sbvExists "poly"
         s <- sbvForall "sent"
         r <- sbvForall "received"
         return $ sTestBit p 0 .&& crcGood 4 p s r
