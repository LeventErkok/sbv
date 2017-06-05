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
  , TimedStep(..)
  , TimingInfo
  , showTDiff
  )
  where

import Control.DeepSeq (rnf, NFData(..))
import Data.Time       (NominalDiffTime, getCurrentTime, diffUTCTime)

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.IORef(IORef, modifyIORef')

import Data.List (intercalate)

import Data.Ratio
import GHC.Real   (Ratio((:%)))

import Numeric (showFFloat)

-- | Specify how to save timing information, if at all.
data Timing     = NoTiming | PrintTiming | SaveTiming (IORef TimingInfo)

-- | Specify what is being timed.
data TimedStep  = ProblemConstruction | Translation | WorkByProver String
                  deriving (Eq, Ord, Show)

-- | A collection of timed stepd.
type TimingInfo = Map TimedStep NominalDiffTime

-- | A more helpful show instance for steps
timedStepLabel :: TimedStep -> String
timedStepLabel lbl =
  case lbl of
    ProblemConstruction -> "problem construction"
    Translation         -> "translation"
    WorkByProver x      -> x

-- Show NominalDiffTime in human readable form. NominalDiffTime is
-- essentially picoseconds (10^-12 seconds). We show it so that
-- it's represented at the day:hour:minute:second.XXX granularity
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
-- to run it. The return type should be an instance of 'NFData' to ensure
-- the correct elapsed time is printed.
timeIf :: NFData a => Timing -> TimedStep -> IO a -> IO a
timeIf how what m =
  case how of
    NoTiming    -> m
    PrintTiming -> do (elapsed, a) <- doTime m
                      putStrLn $ "** Elapsed " ++ timedStepLabel what ++ " time: " ++ showTDiff elapsed
                      return a
    SaveTiming here -> do (elapsed, a) <- doTime m
                          modifyIORef' here (Map.insert what elapsed)
                          return a

doTime :: NFData a => IO a -> IO (NominalDiffTime, a)
doTime m = do start <- getCurrentTime
              r     <- m
              end   <- rnf r `seq` getCurrentTime

              let elapsed = diffUTCTime end start

              elapsed `seq` return (elapsed, r)
