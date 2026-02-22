-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CompileTests.PCase
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing TH messages
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CompileTests.PCase(tests) where

import Utils.SBVTestFramework

tests :: IO TestTree
tests = testGroup "THTests.PCase" <$> mkCompileTestGlob "SBVTestSuite/TestSuite/CompileTests/PCase/PCase*.hs"
