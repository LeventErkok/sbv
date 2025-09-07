-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.THTests.SCase
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing TH messages
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.THTests.SCase(tests) where

import Utils.SBVTestFramework

import System.FilePath
import System.FilePath.Glob (glob)

tests :: IO TestTree
tests = do let testPath = "SBVTestSuite/TestSuite/THTests/Files"
           fs <- glob $ testPath </> "SCase*.hs"
           return $ testGroup "THTests.SCase" (map (mkCompileTest testPath . takeBaseName) fs)
