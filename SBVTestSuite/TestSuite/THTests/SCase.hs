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

tests :: IO TestTree
tests = testGroup "THTests.SCase" <$> mkCompileTestGlob "SBVTestSuite/TestSuite/THTests/Files/SCase*.hs"
