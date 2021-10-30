-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.TDiff
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Runs an IO computation printing the time it took to run it
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Utils.TDiff
  ( Timing(..)
  , showTDiff
  )
  where

import Data.Time  (NominalDiffTime)
import Data.IORef (IORef)

import Data.List (intercalate)

import Data.Ratio
import GHC.Real   (Ratio((:%)))

import Numeric (showFFloat)

-- | Specify how to save timing information, if at all.
data Timing = NoTiming | PrintTiming | SaveTiming (IORef NominalDiffTime)

-- | Show 'NominalDiffTime' in human readable form. 'NominalDiffTime' is
-- essentially picoseconds (10^-12 seconds). We show it so that
-- it's represented at the day:hour:minute:second.XXX granularity.
showTDiff :: NominalDiffTime -> String
showTDiff diff
   | denom /= 1    -- Should never happen! But just in case.
   = show diff
   | True
   = intercalate ":" fields
   where total, denom :: Integer
         total :% denom = (picoFactor % 1) * toRational diff

         -- there are 10^12 pico-seconds in a second
         picoFactor :: Integer
         picoFactor = (10 :: Integer) ^ (12 :: Integer)

         (s2p, m2s, h2m, d2h) = case drop 1 $ scanl (*) 1 [picoFactor, 60, 60, 24] of
                                  (s2pv : m2sv : h2mv : d2hv : _) -> (s2pv, m2sv, h2mv, d2hv)
                                  _                               -> (0, 0, 0, 0)  -- won't ever happen

         (days,    days')    = total    `divMod` d2h
         (hours,   hours')   = days'    `divMod` h2m
         (minutes, seconds') = hours'   `divMod` m2s
         (seconds, picos)    = seconds' `divMod` s2p
         secondsPicos        =  show seconds
                             ++ dropWhile (/= '.') (showFFloat (Just 3) (fromIntegral picos * (10**(-12) :: Double)) "s")

         aboveSeconds = map (\(t, v) -> show v ++ [t]) $ dropWhile (\p -> snd p == 0) [('d', days), ('h', hours), ('m', minutes)]
         fields       = aboveSeconds ++ [secondsPicos]
