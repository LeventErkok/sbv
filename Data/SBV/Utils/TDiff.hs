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
import System.Time     (TimeDiff(..), normalizeTimeDiff, diffClockTimes, getClockTime)
import Numeric         (showFFloat)

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.IORef(IORef, modifyIORef')

-- | Specify how to save timing information, if at all.
data Timing     = NoTiming | PrintTiming | SaveTiming (IORef TimingInfo)

-- | Specify what is being timed.
data TimedStep  = ProblemConstruction | Translation | WorkByProver String
                  deriving (Eq, Ord, Show)

-- | A collection of timed stepd.
type TimingInfo = Map TimedStep TimeDiff

-- | A more helpful show instance for steps
timedStepLabel :: TimedStep -> String
timedStepLabel lbl =
  case lbl of
    ProblemConstruction -> "problem construction"
    Translation         -> "translation"
    WorkByProver x      -> x

-- | Show the time difference in a user-friendly format.
showTDiff :: TimeDiff -> String
showTDiff itd = et
  where td = normalizeTimeDiff itd
        vals = dropWhile (\(v, _) -> v == 0) (zip [tdYear td, tdMonth td, tdDay td, tdHour td, tdMin td] "YMDhm")
        sec = ' ' : show (tdSec td) ++ dropWhile (/= '.') pico
        pico = showFFloat (Just 3) (((10**(-12))::Double) * fromIntegral (tdPicosec td)) "s"
        et = concatMap (\(v, c) -> ' ':show v ++ [c]) vals ++ sec

-- | If selected, runs the computation @m@, and prints the time it took
-- to run it. The return type should be an instance of 'NFData' to ensure
-- the correct elapsed time is printed.
timeIf :: NFData a => Timing -> TimedStep -> IO a -> IO a
timeIf how what m =
  case how of
    NoTiming -> m
    PrintTiming ->
      do (elapsed,a) <- doTime m
         putStrLn $ "** Elapsed " ++ timedStepLabel what ++ " time:" ++ showTDiff elapsed
         return a
    SaveTiming here ->
      do (elapsed,a) <- doTime m
         modifyIORef' here (Map.insert what elapsed)
         return a

doTime :: NFData a => IO a -> IO (TimeDiff,a)
doTime m = do start <- getClockTime
              r <- m
              end <- rnf r `seq` getClockTime
              let elapsed = diffClockTimes end start
              elapsed `seq` return (elapsed, r)
