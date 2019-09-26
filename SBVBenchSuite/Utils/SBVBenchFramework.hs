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

module Utils.SBVBenchFramework
  ( mkExecString
  , mkFileName
  , module Criterion.Main
  , module Data.SBV
  ) where

import qualified Data.List      as L
import           System.Process (showCommandForUser)
import           System.Random

import           Criterion.Main (Benchmark, bgroup)

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
