-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Optimization.Enumerate
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates how enumerations can be used with optimization,
-- by properly defining your metric values.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Optimization.Enumerate where

import Data.SBV

-- | A simple enumeration
data Day = Mon | Tue | Wed | Thu | Fri | Sat | Sun

-- | Make 'Day' a symbolic value.
mkSymbolicEnumeration ''Day

-- | Make day an optimizable value, by mapping it to 'Word8' in the most
-- obvious way. We can map it to any value the underlying solver can optimize,
-- but 'Word8' is the simplest and it'll fit the bill.
instance Metric Day where
  type MetricSpace Day = Word8

  toMetricSpace x   = ite (x .== sMon) 0
                    $ ite (x .== sTue) 1
                    $ ite (x .== sWed) 2
                    $ ite (x .== sThu) 3
                    $ ite (x .== sFri) 4
                    $ ite (x .== sSat) 5
                                       6

  fromMetricSpace x = ite (x .== 0) sMon
                    $ ite (x .== 1) sTue
                    $ ite (x .== 2) sWed
                    $ ite (x .== 3) sThu
                    $ ite (x .== 4) sFri
                    $ ite (x .== 5) sSat
                                    sSun

-- | Identify weekend days
isWeekend :: SDay -> SBool
isWeekend = (`sElem` weekend)
  where weekend = [sSat, sSun]

-- | Using optimization, find the latest day that is not a weekend.
-- We have:
--
-- >>> almostWeekend
-- Optimal model:
--   almostWeekend = Fri :: Day
--   last-day      =   4 :: Word8
almostWeekend :: IO OptimizeResult
almostWeekend = optimize Lexicographic $ do
                    day <- free "almostWeekend"
                    constrain $ sNot (isWeekend day)
                    maximize "last-day" day

-- | Using optimization, find the first day after the weekend.
-- We have:
--
-- >>> weekendJustOver
-- Optimal model:
--   weekendJustOver = Mon :: Day
--   first-day       =   0 :: Word8
weekendJustOver :: IO OptimizeResult
weekendJustOver = optimize Lexicographic $ do
                      day <- free "weekendJustOver"
                      constrain $ sNot (isWeekend day)
                      minimize "first-day" day

-- | Using optimization, find the first weekend day:
-- We have:
--
-- >>> firstWeekend
-- Optimal model:
--   firstWeekend  = Sat :: Day
--   first-weekend =   5 :: Word8
firstWeekend :: IO OptimizeResult
firstWeekend = optimize Lexicographic $ do
                      day <- free "firstWeekend"
                      constrain $ isWeekend day
                      minimize "first-weekend" day
