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

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-methods #-} -- for ProvableM orphan

module Utils.SBVBenchFramework
  ( mkExecString
  , mkFileName
  , module Data.SBV
  , timeStamp
  , getDate
  , dateStamp
  , benchResultsFile
  , classifier
  , overheadClassifier
  , filterOverhead
  ) where

import qualified Data.List      as L
import           System.Process (showCommandForUser)
import           System.Random
import           Data.Char (isSpace)
import           System.FilePath ((</>), (<.>))
import           Data.Time.Clock
import           Data.Time.Calendar

import           Data.SBV
import           Data.SBV.Internals

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
benchResultsFile nm = "SBVBenchSuite" </> "BenchResults" </> nm <.> "csv"

-- | The classifier takes a line of text and chunks it into (group-name,
-- benchmark-name), for example:
classifier :: Char -> String -> Maybe (String, String)
classifier e nm = Just $ last chunks
  where
    is :: [Int]
    is = L.elemIndices e nm

    chunks = [(a, drop 1 b) | (a, b) <- fmap (`L.splitAt` nm) is]

-- | We live with some code duplication due to the way overhead benchmarks apply
-- the "standalone" and "sbv" labels. By abstracting for overhead benchmarks
-- these labels will be appended to the description string. This is counter to
-- the assumptions of the bench-show package, thus we define a specialty
-- classifier to handle the overhead case
overheadClassifier :: Char -> String -> Maybe (String, String)
overheadClassifier e nm = Just $ last $ fmap (\(a,b) -> (drop 1 b, a)) chunks
  where
    is :: [Int]
    is = L.elemIndices e nm

    chunks = fmap (`L.splitAt` nm) is

-- | a helper function to remove benchmarks where the over head benchmark
-- doesn't work or failed for some reason. This will write a filtered version
-- and return the file path to that filtered version.
filterOverhead :: Char -> FilePath -> IO FilePath
filterOverhead e fp = do (header:file) <- L.lines <$> readFile fp
                         -- only keep instances of 3 or greater. This number
                         -- comes from splitting benchmark output by '/'.
                         -- Because our groups are separated by '//' and the
                         -- overhead by '/' an overhead run will have >3 splits,
                         -- but a normal benchmark will only have two from '//'
                         let filteredContent   = filter ((>=3) . length . L.elemIndices e) file
                             filteredFilePath  = fp ++ "_filtered"
                         writeFile  filteredFilePath (concat $ header:filteredContent)
                         return filteredFilePath

-- NO INSTANCE ON PURPOSE; don't want to prove goals. We provide this instance
-- just to allow the testsuite to run tests with try to Prove Goals. In general,
-- this violates the invariants promised by the @ProvableM@ and @SatisfiableM@
-- type classes. Thus, this should not be publicly exposed under any
-- circumstances.
instance ProvableM IO (SymbolicT IO ())
