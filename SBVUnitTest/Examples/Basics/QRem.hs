-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.Basics.QRem
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing the qrem (quote-rem) function
-----------------------------------------------------------------------------

module Examples.Basics.QRem where

import Data.SBV

-- check: if (a, b) = x `quotRem` y then x = y*a + b
-- being careful about y = 0. When divisor is 0, then quotient is
-- defined to be 0 and the remainder is the numerator
qrem :: (Num a, EqSymbolic a, BVDivisible a) => a -> a -> SBool
qrem x y = ite (y .== 0) ((0, x) .== (a, b)) (x .== y * a + b)
  where (a, b) = x `bvQuotRem` y

check :: IO ()
check = print =<< prove (qrem :: SWord8 -> SWord8 -> SBool)
         -- print =<< prove (qrem :: SWord16 -> SWord16 -> SBool)   -- takes too long!
