-----------------------------------------------------------------------------
-- |
-- Module    : Utils.SBVTestFramework
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various goodies for benchmarking SBV
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Utils.SBVBenchFramework
  ( mkExecString
  , mkFileName
  , Benchmark
  , bgroup
  , module Data.SBV
  , timeStamp
  , getDate
  , dateStamp
  , benchResultsFile
  , compareBenchMarksCli
  ) where

import qualified Data.List      as L
import           System.Process (showCommandForUser)
import           System.Random
import           Data.Char (isSpace)
import           System.FilePath ((</>), (<.>))
import           Data.Ord (comparing)
import           Data.Time.Clock
import           Data.Time.Calendar

import           Gauge.Main (Benchmark, bgroup)
import qualified BenchShow as BS hiding (verbose)

import           Data.SBV

-- | make the string to call executable from the command line. All the heavy
-- lifting is done by 'System.Process.showCommandForUser', the rest is just
-- projections out of 'Data.SBV.SMTConfig'
mkExecString :: SMTConfig -> FilePath -> String
mkExecString config inputFile = showCommandForUser exec $ inputFile:opts
  where smtSolver = solver config
        exec      = executable smtSolver
        opts'     = options smtSolver config
        opts      = L.delete "-in" opts' -- remove opt for interactive mode so
                                         -- that this plays nice with
                                         -- criterion environments

-- | simple wrapper to create random file names.
mkFileName :: IO String
mkFileName = do gen <- newStdGen
                return . take 32 $ randomRs ('a','z') gen


-- | Get (year, month, day)
getDate :: IO (Integer, Int, Int)
getDate = toGregorian . utctDay <$> getCurrentTime

dateStamp :: IO String
dateStamp = (\(y,m,d) -> show y ++ "-" ++
                         show m ++ "-" ++
                         show d) <$> getDate

-- | Construct a timestamp
timeStamp :: IO String
timeStamp = fmap (spaceTo '-') . show <$> getCurrentTime

spaceTo :: Char -> Char -> Char
spaceTo c x | isSpace x = c
            | otherwise = x

-- | Construct a benchmark file name. The input name should be a time stamp or
-- whatever you want to name the benchmark
benchResultsFile :: FilePath -> FilePath
benchResultsFile nm = "SBVBenchSuite" </> "BenchFiles" </> nm <.> "csv"

-- | Run bench-show comparisons on a given file. Bench show expects comparisons
-- to be in a single file and differentiates the runs by a header generated from
-- either @gauge@ or @criterion@. For
-- <http://hackage.haskell.org/package/bench-show-0.3.1 bench-show> for more
-- details.
compareBenchMarksCli :: FilePath -> IO ()
compareBenchMarksCli fp = BS.report fp Nothing
                          BS.defaultConfig
                          { BS.classifyBenchmark = classfier '/'
                          , BS.presentation = BS.Groups BS.PercentDiff
                          , BS.selectBenchmarks = \f ->
                              reverse
                              $ map fst
                              $ L.sortBy (comparing snd)
                              $ either error id
                              $ f (BS.ColumnIndex 1) Nothing}
  where
   classfier :: Char -> String -> Maybe (String, String)
   classfier e nm = i >>= return . flip L.splitAt nm
     where i = L.elemIndex e nm
