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
  , classifier
  , filterOverhead
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
                          { BS.classifyBenchmark = classifier '/'      -- separate groups by slashes
                          , BS.presentation = BS.Groups BS.PercentDiff -- report percent difference
                          , BS.selectBenchmarks = \f ->                -- sort from Improvement - Degradation
                              map fst
                              $ L.sortBy (comparing snd)
                              $ either error id
                              $ f (BS.ColumnIndex 1) Nothing
                          }


-- | The classifier takes a line of text and chunks it into (group-name,
-- benchmark-name), for example:
--
-- >>> classifier '/' "Puzzles//DogCatMouse/standalone"
-- Just ("standalone","Puzzles//DogCatMouse")
--
classifier :: Char -> String -> Maybe (String, String)
classifier e nm = Just $ last $ fmap (\(a,b) -> (tail b, a)) chunks
  where
    is :: [Int]
    is = L.elemIndices e nm

    chunks = fmap (flip L.splitAt nm) is

-- | a helper function to remove benchmarks where the over head benchmark
-- doesn't work or failed for some reason. This will write a filtered version
-- and return the file path to that filtered version.
filterOverhead :: Char -> FilePath -> IO FilePath
filterOverhead e fp = do (header:file) <- L.lines <$> readFile fp
                         -- only keep instances of 3 or greated. This number
                         -- comes from splitting benchmark output by '/'.
                         -- Because our groups are separated by '//' and the
                         -- overhead by '/' an overhead run will have >3 splits,
                         -- but a normal benchmark will only have two from '//'
                         let filteredContent   = filter ((>=3) . length . L.elemIndices e) file
                             filteredFilePath  = (fp ++ "_filtered")
                         writeFile  filteredFilePath (concat $ header:filteredContent)
                         return filteredFilePath
