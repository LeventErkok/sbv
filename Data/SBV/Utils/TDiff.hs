{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Utils.TDiff(timeIf) where

import Control.Parallel.Strategies
import System.Time
import Numeric

showTDiff :: TimeDiff -> String
showTDiff itd = et
  where td = normalizeTimeDiff itd
        vals = dropWhile (\(v, _) -> v == 0) (zip [tdYear td, tdMonth td, tdDay td, tdHour td, tdMin td] "YMDhm")
        sec = ' ' : show (tdSec td) ++ dropWhile (/= '.') pico
        pico = showFFloat (Just 3) (((10**(-12))::Double) * fromIntegral (tdPicosec td)) "s"
        et = concatMap (\(v, c) -> ' ':show v ++ [c]) vals ++ sec

timeIf :: NFData a => Bool -> String -> IO a -> IO a
timeIf False _ m = m
timeIf True  w m = do start <- getClockTime
                      r <- m
                      end <- rnf r `seq` getClockTime
                      let elapsed = diffClockTimes end start
                      putStrLn $ "** Elapsed " ++ w ++ " time:" ++ showTDiff elapsed
                      return r
