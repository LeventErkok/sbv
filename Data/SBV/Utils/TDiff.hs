-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Utils.TDiff
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Runs an IO computation printing the time it took to run it
-----------------------------------------------------------------------------

module Data.SBV.Utils.TDiff
  ( timeIf
  , Timing(..)
  , showTDiff
  )
  where

import Data.Time  (NominalDiffTime, getCurrentTime, diffUTCTime)
import Data.IORef (IORef, writeIORef)

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

         [s2p, m2s, h2m, d2h] = drop 1 $ scanl (*) 1 [picoFactor, 60, 60, 24]

         (days,    days')    = total    `divMod` d2h
         (hours,   hours')   = days'    `divMod` h2m
         (minutes, seconds') = hours'   `divMod` m2s
         (seconds, picos)    = seconds' `divMod` s2p
         secondsPicos        =  show seconds
                             ++ dropWhile (/= '.') (showFFloat (Just 3) (fromIntegral picos * (10**(-12) :: Double)) "s")

         aboveSeconds = map (\(t, v) -> show v ++ [t]) $ dropWhile (\p -> snd p == 0) [('d', days), ('h', hours), ('m', minutes)]
         fields       = aboveSeconds ++ [secondsPicos]

-- | If selected, runs the computation @m@, and prints the time it took
-- to run it. The odd second argument is simply there to force the result,
-- and is typically just @rnf@. But @(`seq` ())@ will also do if 'rnf' isn't
-- available for some reason and the WHNF is sufficient.
timeIf :: Timing -> (a -> ()) -> IO a -> IO a
timeIf how serialize m =
  case how of
    NoTiming         -> m
    PrintTiming      -> do (elapsed, a) <- doTime serialize m
                           putStrLn $ "** Elapsed time: " ++ showTDiff elapsed
                           return a
    SaveTiming here -> do (elapsed, a) <- doTime serialize m
                          writeIORef here elapsed
                          return a

doTime :: (a -> ()) -> IO a -> IO (NominalDiffTime, a)
doTime serialize m = do start <- getCurrentTime
                        r     <- m
                        end   <- serialize r `seq` getCurrentTime

                        let elapsed = diffUTCTime end start

                        elapsed `seq` return (elapsed, r)
