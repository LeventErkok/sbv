-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.SendMoreMoney
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the classic @send + more = money@ puzzle.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.SendMoreMoney where

import Data.SBV

-- | Solve the puzzle. We have:
--
-- >>> sendMoreMoney
-- Solution #1:
--   s = 9 :: Integer
--   e = 5 :: Integer
--   n = 6 :: Integer
--   d = 7 :: Integer
--   m = 1 :: Integer
--   o = 0 :: Integer
--   r = 8 :: Integer
--   y = 2 :: Integer
-- This is the only solution.
--
-- That is:
--
-- >>> 9567 + 1085 == 10652
-- True
sendMoreMoney :: IO AllSatResult
sendMoreMoney = allSat $ do
        ds@[s,e,n,d,m,o,r,y] <- mapM sInteger ["s", "e", "n", "d", "m", "o", "r", "y"]
        let isDigit x = x .>= 0 .&& x .<= 9
            val xs    = sum $ zipWith (*) (reverse xs) (iterate (*10) 1)
            send      = val [s,e,n,d]
            more      = val [m,o,r,e]
            money     = val [m,o,n,e,y]
        constrain $ sAll isDigit ds
        constrain $ distinct ds
        constrain $ s ./= 0 .&& m ./= 0
        solve [send + more .== money]
