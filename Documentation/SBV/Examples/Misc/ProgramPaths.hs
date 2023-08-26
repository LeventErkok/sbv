-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.ProgramPaths
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A simple example of showing how to compute program paths. Consider the simple
-- program:
-- 
-- @
--   d1 x y = if y < x - 2  then   7 else   2
--   d2   y = if y > 3      then  10 else  50
--   d3 x y = if y < -x + 3 then 100 else 200
--   d4 x y = d1 x y + d2 y + d3 x y
-- @
--
-- What are all the possible values @d4 x y@ can take, and what are the values of
-- @x@ and @y@ to obtain these values?
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.ProgramPaths where

import Data.SBV

-- | Symbolic version of @d1 x y = if y < x - 2 then 7 else 2@
d1 :: SInteger -> SInteger -> SInteger
d1 x y = ite (y .< x - 2) 7 2

-- | Symbolic version of @d2 x y = if y > 3 then  10 else  50@
d2 :: SInteger -> SInteger
d2 y = ite (y .> 3) 10 50

-- | Symbolic version of @d3 x y = if y < -x + 3 then 100 else 200@
d3 :: SInteger -> SInteger -> SInteger
d3 x y = ite (y .< -x + 3) 100 200

-- | Symbolic version of @d4 x y = d1 x y + d2 x y + d3 x y@
d4 :: SInteger -> SInteger -> SInteger
d4 x y = d1 x y + d2 y + d3 x y

-- | Compute all possible program paths. Note the call to `partition`, which
-- causes `allSat` to find models that generate differing values for the given
-- expression. We have:
--
-- >>> paths
-- Solution #1:
--   x =  -2 :: Integer
--   y =   4 :: Integer
--   r = 112 :: Integer
-- Solution #2:
--   x =   0 :: Integer
--   y =   3 :: Integer
--   r = 252 :: Integer
-- Solution #3:
--   x =  -1 :: Integer
--   y =   4 :: Integer
--   r = 212 :: Integer
-- Solution #4:
--   x =   3 :: Integer
--   y =   0 :: Integer
--   r = 257 :: Integer
-- Solution #5:
--   x =   2 :: Integer
--   y =  -1 :: Integer
--   r = 157 :: Integer
-- Solution #6:
--   x =   7 :: Integer
--   y =   4 :: Integer
--   r = 217 :: Integer
-- Solution #7:
--   x =   0 :: Integer
--   y =   0 :: Integer
--   r = 152 :: Integer
-- Found 7 different solutions.
paths :: IO AllSatResult
paths = allSat $ do
  x <- sInteger "x"
  y <- sInteger "y"
  partition "r" $ d4 x y
