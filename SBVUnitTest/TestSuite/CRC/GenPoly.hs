-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.GenPoly
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.CRC.GenPoly
-----------------------------------------------------------------------------

module TestSuite.CRC.GenPoly(tests) where

import Data.SBV

import Examples.CRC.GenPoly
import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "CRC.GenPoly"
    [   testCase "crcGoodE" (assertIsSat crcGoodE)
      , testCase "crcGood" (assertIsntThm (crcGood 3 12))
    ]

crcGoodE :: Symbolic SBool
crcGoodE = do
  x1 <- exists_
  x2 <- exists_
  y1 <- exists_
  y2 <- exists_
  return (crcGood 3 0 (x1,x2) (y1,y2))
