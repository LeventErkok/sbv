-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.QuickCheck.QC
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Quick-check based test suite for SBV
-----------------------------------------------------------------------------

module TestSuite.QuickCheck.QC (tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "QuickCheck.QC" $ qc2 "+.SWord8" (+) ((+) :: SWord8 -> SWord8 -> SWord8)
