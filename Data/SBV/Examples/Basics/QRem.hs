{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Examples.Basics.QRem where

import Data.SBV
import Data.SBV.Utils.SBVTest

-- check: if (a, b) = x `quotRem` y then x = y*a + b
-- being careful about y = 0. When divisor is 0, then quotient is
-- defined to be 0 and the remainder is the numerator
qrem :: (Num a, EqSymbolic a, BVDivisible a) => a -> a -> SBool
qrem x y = ite (y .== 0) ((0, x) .== (a, b)) (x .== y * a + b)
  where (a, b) = x `bvQuotRem` y

main :: IO ()
main = do print =<< prove (qrem :: SWord8 -> SWord8 -> SBool)
          -- print =<< prove (qrem :: SWord16 -> SWord16 -> SBool)   -- takes too long!

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "qrem" ~: assert =<< isTheorem (qrem :: SWord8 -> SWord8 -> SBool)
 ]
