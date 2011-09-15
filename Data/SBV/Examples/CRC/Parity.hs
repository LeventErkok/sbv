-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CRC.Parity
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Parity check as CRC's
-----------------------------------------------------------------------------

module Data.SBV.Examples.CRC.Parity where

import Data.SBV

parity :: SWord64 -> SBool
parity x = bnot (isOdd cnt)
  where cnt :: SWord8
        cnt = count (blastLE x)

isOdd :: SWord8 -> SBool
isOdd x = lsb x .== true

-- count the true bits
count :: [SBool] -> SWord8
count []     = 0
count (x:xs) = let c' = count xs in ite x (1+c') c'

-- Example suggested by Lee Pike
-- If x and y differ in odd-number of bits, then their parities are flipped
parityOK :: SWord64 -> SWord64 -> SBool
parityOK x y = isOdd cnt ==> px .== bnot py
  where cnt = count (zipWith (./=) (blastLE x) (blastLE y))
        px  = parity x
        py  = parity y
