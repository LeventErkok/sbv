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

module Documentation.SBV.Examples.Optimization.Enumerate where

import Data.SBV

-- | A simple enumeration
data Day = Mon | Tue | Wed | Thu | Fri | Sat | Sun

-- | Make 'Day' a symbolic value.
mkSymbolicEnumeration ''Day

-- | Give a name to the symbolic variants of 'Day', for convenience
type SDay = SBV Day

-- | Make day an optimizable value, by mapping it to 'Word8' in the most
-- obvious way. We can map it to any value the underlying solver can optimize,
-- but 'Word8' is the simplest and it'll fit the bill.
instance Metric Day where
  type MetricSpace Day = Word8

  toMetricSpace x   = ite (x .== literal Mon) 0
                    $ ite (x .== literal Tue) 1
                    $ ite (x .== literal Wed) 2
                    $ ite (x .== literal Thu) 3
                    $ ite (x .== literal Fri) 4
                    $ ite (x .== literal Sat) 5
                                              6

  fromMetricSpace x = ite (x .== 0) (literal Mon)
                    $ ite (x .== 1) (literal Tue)
                    $ ite (x .== 2) (literal Wed)
                    $ ite (x .== 3) (literal Thu)
                    $ ite (x .== 4) (literal Fri)
                    $ ite (x .== 5) (literal Sat)
                                    (literal Sun)

-- | Identify weekend days
isWeekend :: SDay -> SBool
isWeekend = (`sElem` weekend)
  where weekend = map literal [Sat, Sun]

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
