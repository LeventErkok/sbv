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
  )
  where

import Control.DeepSeq (rnf, NFData(..))
import Data.Time       (NominalDiffTime, getCurrentTime, diffUTCTime)

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.IORef(IORef, modifyIORef')

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

-- | If selected, runs the computation @m@, and prints the time it took
-- to run it. The return type should be an instance of 'NFData' to ensure
-- the correct elapsed time is printed.
timeIf :: NFData a => Timing -> TimedStep -> IO a -> IO a
timeIf how what m =
  case how of
    NoTiming    -> m
    PrintTiming -> do (elapsed, a) <- doTime m
                      putStrLn $ "** Elapsed " ++ timedStepLabel what ++ " time: " ++ show elapsed
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
