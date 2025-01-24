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

{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Utils.TDiff
  ( Timing(..)
  , timeIf
  , timeIfRNF
  , showTDiff
  , getTimeStampIf
  , getElapsedTime
  )
  where

import Data.Time (getCurrentTime, diffUTCTime, NominalDiffTime, UTCTime)
import Data.IORef (IORef)

import Data.List (intercalate)

import Data.Ratio
import GHC.Real   (Ratio((:%)))

import Numeric (showFFloat)

import Control.Monad.Trans (liftIO, MonadIO)
import Control.DeepSeq (NFData(rnf))


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

-- | Run an action and measure how long it took. We reduce the result to weak-head-normal-form,
-- so beware of the cases if the result is lazily computed; in which case we'll stop soon as the
-- result is in WHNF, and not necessarily fully calculated.
timeIf :: MonadIO m => Bool -> m a -> m (Maybe NominalDiffTime, a)
timeIf measureTime act = do mbStart <- getTimeStampIf measureTime
                            r     <- act
                            r `seq` do mbElapsed <- getElapsedTime mbStart
                                       pure (mbElapsed, r)

-- | Same as 'timeIf', except we fully evaluate the result, via its the NFData instance.
timeIfRNF :: (NFData a, MonadIO m) => Bool -> m a -> m (Maybe NominalDiffTime, a)
timeIfRNF measureTime act = timeIf measureTime (act >>= \r -> rnf r `seq` pure r)

-- | Get a time-stamp if we're asked to do so
getTimeStampIf  :: MonadIO m => Bool -> m (Maybe UTCTime)
getTimeStampIf measureTime
  | not measureTime = pure Nothing
  | True            = liftIO $ Just <$> getCurrentTime

-- | Get elapsed time from the given beginning time, if any.
getElapsedTime :: MonadIO m => Maybe UTCTime -> m (Maybe NominalDiffTime)
getElapsedTime Nothing      = pure Nothing
getElapsedTime (Just start) = liftIO $ do e <- getCurrentTime
                                          pure $ Just (diffUTCTime e start)
