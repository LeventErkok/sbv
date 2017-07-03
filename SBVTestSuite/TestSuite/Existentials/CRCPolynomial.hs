-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Existentials.CRCPolynomial
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Existentials.CRCPolynomial
-----------------------------------------------------------------------------

module TestSuite.Existentials.CRCPolynomial(tests) where

import Data.SBV.Examples.Existentials.CRCPolynomial

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Existentials.CRCPolynomial" [
  goldenVsStringShow "crcPolyExist" pgm
 ]
 where pgm = runSAT $ do
                p <- exists "poly"
                s <- do sh <- forall "sh"
                        sl <- forall "sl"
                        return (sh, sl)
                r <- do rh <- forall "rh"
                        rl <- forall "rl"
                        return (rh, rl)
                output $ sTestBit p 0 &&& crcGood 4 p s r
