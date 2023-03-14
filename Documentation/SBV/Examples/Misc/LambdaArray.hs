-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.LambdaArray
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates how lambda-abstractions can be used to model arrays.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.LambdaArray where

import Data.SBV

-- | Given an array, and bounds on it, initialize it within the bounds to the element given.
-- Otherwise, leave it untouched.
memset :: SArray Integer Integer -> SInteger -> SInteger -> SInteger -> Symbolic (SArray Integer Integer)
memset mem lo hi newVal = lambdaAsArray update
  where update :: SInteger -> SInteger
        update idx = let oldVal = readArray mem idx
                     in ite (lo .<= idx .&& idx .<= hi) newVal oldVal

-- | Prove a simple property: If we read from the initialized region, we get the initial value. We have:
--
-- >>> memsetExample
-- Q.E.D.
memsetExample :: IO ThmResult
memsetExample = prove $ do
   mem  <- newArray "mem" Nothing

   lo   <- sInteger "lo"
   hi   <- sInteger "hi"
   zero <- sInteger "zero"

   -- initialize lo-hi to zero. Otherwise free.
   initialized <- memset mem lo hi zero

   -- Get an index within lo/hi
   idx  <- sInteger "idx"
   constrain $ idx .>= lo .&& idx .<= hi

   -- It must be the case that we get zero back
   pure $ readArray initialized idx .== zero

-- | Get an example of reading a value out of range. The value returned should be out-of-range for lo/hi
--
-- >>> outOfInit
-- Satisfiable. Model:
--   lo   = 0 :: Integer
--   hi   = 0 :: Integer
--   zero = 0 :: Integer
--   idx  = 1 :: Integer
outOfInit :: IO SatResult
outOfInit = sat $ do
   mem  <- newArray "mem" Nothing

   lo   <- sInteger "lo"
   hi   <- sInteger "hi"
   zero <- sInteger "zero"

   -- initialize lo-hi to zero. Otherwise free.
   constrain $ lo .<= hi
   initialized <- memset mem lo hi zero

   -- Get an index within lo/hi
   idx  <- sInteger "idx"

   -- Let read produce non-zero
   constrain $ readArray initialized idx ./= zero
