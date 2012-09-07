-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.Basics.QRem
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing the sQuotRem and sDivMod
-----------------------------------------------------------------------------

module Examples.Basics.QRem where

import Data.SBV

-- check: if (a, b) = x `quotRem` y then x = y*a + b
-- same is also true for divMod
-- being careful about y = 0. When divisor is 0, then quotient is
-- defined to be 0 and the remainder is the numerator
qrem :: (Num a, EqSymbolic a, SDivisible a) => a -> a -> SBool
qrem x y = ite (y .== 0)
               ((0, x) .== (q, r) &&& (0, x) .== (d, m))
               (x .== y * q + r &&& x .== y * d + m)
  where (q, r) = x `sQuotRem` y
        (d, m) = x `sDivMod` y

check :: IO ()
check = do print =<< prove (qrem :: SWord8   -> SWord8   -> SBool)
           print =<< prove (qrem :: SInt8    -> SInt8    -> SBool)
           print =<< prove (qrem :: SInteger -> SInteger -> SBool)
