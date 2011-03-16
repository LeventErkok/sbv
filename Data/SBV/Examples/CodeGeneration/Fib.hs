-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CodeGeneration.AddSub.hs
-- Copyright   :  (c) Lee Pike
-- License     :  BSD3
-- Maintainer  :  leepike@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Different ways to write the Fibonacci sequence (modulo Word8)---we
-- ignore overflow in the following---using SBV.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.CodeGeneration.Fib where

import Data.SBV

-- | This function is a perfectly valid Haskell function, and you can evaluate
-- it; e.g.,
-- 
-- >>> map (fib0 . fromIntegral) [0..6]
-- 
-- yields the first 6 values of the Fibonacci sequence:
--
-- @ 
-- [0 :: SWord8,1 :: SWord8,1 :: SWord8,2 :: SWord8,3 :: SWord8,5 :: SWord8,8 :: SWord8]
-- @
--
-- However, we cannot generate code from this function, since the conditions in
-- the ite expressions do not symbolically terminate---symbolically, there's no
-- way to know that fib0 terminates (other than through realizing that it's type
-- is finite).  Trying to generate code loop forever.
fib0 :: SWord8 -> SWord8
fib0 n = 
  ite (n .== 0) 0 
      (ite (n .== 1) 1
           (fib0 (n-1) + fib0 (n-2)))

{-
-- Won't terminate!
gen :: IO ()  
gen = compileToC True (Just "fib") "fib" [] (\(x::SWord8) -> fib1 x)
-}

-- | This function takes two inputs, a maximum index to compute and the index
-- into the Fibonacci sequence to be returned.  This function is also a valid
-- Haskell function that can be evaluated as above; e.g.,
-- 
-- >>> map ((fib1 20) . fromIntegral) [0..6]
-- 
-- But 'fib1' symbolically terminates after unrolling @fib'@ @top@ times.  Thus,
-- we can generate code for the function, using 'compile1' below.
fib1 :: SWord8 -> SWord8 -> SWord8
fib1 top n = fib' (0,1) 0 
  where fib' :: (SWord8,SWord8) -> SWord8 -> SWord8
        fib' (acc2,acc1) m = 
          ite (m .== top) acc2
              (fib' ( ite (n .> m) acc1 acc2
                    , ite (n .> m) (acc1 + acc2) acc1)
                    (m+1))

compile1 :: SWord8 -> IO ()  
compile1 top = 
  compileToC True (Just "fib1") "fib1" [] (\(x::SWord8) -> fib1 top x)

-- | 'fib1' computes Fibonacci, but the C code is not efficient insofar as the
-- length of time required to compute a value (during the execution of the C
-- code) is always proportional to the upper-bound given.  We can do better if
-- we realize that we can compute the values of the sequence at evaluation time
-- (of the Haskell function), then just look up the index in the generated
-- table.  The following function does just this: we generate the table using
-- 'fib0'---remember, 'fib0' is just a Haskell function that computes
-- Fibonacci---and then we select the right element from the list at runtime of
-- the C code.  This generates constant-time C code.  Here's the code for
--
-- >>> compile2 20
--
-- @
-- SWord8 fib2(const SWord8 s0)
-- {
--   static const SWord8 table0[] = {
--       0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 121, 98, 219,
--       61, 24, 85, 109
--   };
--   const SWord8 s21 = s0 >= 21 ? 0 : table0[s0];
--   return s21;
-- }
-- @
--
fib2 :: Int -> SWord8 -> SWord8
fib2 top n =
  let table = map (fib0 . fromIntegral) [0..top] in
  select table 0 n

compile2 :: Int -> IO ()  
compile2 top = 
  compileToC True (Just "fib2") "fib2" [] (\(x::SWord8) -> fib2 top x)
