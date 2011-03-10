-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CodeGeneration.PopulationCount
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Computing population-counts (number of set bits) and autimatically
-- generating C code.
-----------------------------------------------------------------------------

module Data.SBV.Examples.CodeGeneration.PopulationCount where

import Data.SBV

-----------------------------------------------------------------------------
-- * Reference: Slow but /obviously/ correct
-----------------------------------------------------------------------------

-- | Given a 64-bit quantity, the simplest (and obvious) way to count the
-- number of bits that are set in it is to simply walk through all the bits
-- and add 1 to a running count. This is slow, as it requires 64 iterations,
-- but is simple and easy to convince yourself that it is correct.
--
-- Example:
--
-- >>> popCount_Slow 0x0123456789ABCDEF
-- 32
--
-- As you can verify by writing the above in binary and counting the 1's in it.
popCount_Slow :: SWord64 -> SWord8
popCount_Slow inp = go inp 0 0
  where go x 64 c = c
        go x i  c = go (x `shiftR` 1) (i+1) (ite (x .&. 1 .== 1) (c+1) c)

-----------------------------------------------------------------------------
-- * Faster: Using a look-up table
-----------------------------------------------------------------------------

-- | Faster version. This is essentially the same algorithm, except we
-- go 8 bits at a time instead of one by one, by using a precomputed table
-- of population-count values for each byte. This algorithm /loops/ only
-- 8 times, and goes in bytes, and hence is more efficient.
popCount :: SWord64 -> SWord8
popCount inp = go inp 0 0
  where go x 8 c = c
        go x i c = go (x `shiftR` 8) (i+1) (c + select pop8 0 (x .&. 0xff))


-- | Look-up table, containing population counts for all possible 8-bit
-- value, from 0 to 255.
pop8 :: [SWord8]
pop8 = [ 0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4,
         1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
         1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
         2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
         1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
         2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
         2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
         3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
         1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
         2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
         2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
         3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
         2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
         3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
         3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
         4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8
       ]

-----------------------------------------------------------------------------
-- * Verification
-----------------------------------------------------------------------------

-- | While we would like to use `popCount` instead of `popCount_Slow`, how can
-- we be absolutely sure that we got the constants correctly computed and
-- stored in `pop8`? It is entirely possible that one of the entries might
-- be incorrect, causing a hard-to-detect bug. However, using SBV we can equivalence
-- check that the faster version computes precisely the same answers as the slower
-- reference version.
--
-- We have:
--
-- >>> prove fastPopCountIsCorrect
-- Q.E.D.
fastPopCountIsCorrect :: IO ThmResult
fastPopCountIsCorrect = \x -> popCount x .== popCount_Slow x

-----------------------------------------------------------------------------
-- * Code generation
-----------------------------------------------------------------------------

-- | Not only we can prove that faster version is correct, but we can also automatically
-- generate C code to compute population-counts for us. This action will generate all the
-- C files that you will need, including a driver program for test purposes.
genPopCountInC :: IO ()
genPopCountInC = compileToC False (Just "popCountC") ["x", "pc"] popCount
