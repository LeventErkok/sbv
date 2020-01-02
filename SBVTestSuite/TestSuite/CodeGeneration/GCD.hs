-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.GCD
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.CodeGeneration.GCD
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.GCD(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.CodeGeneration.GCD

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CodeGeneration.GCD" [
   goldenVsStringShow "gcd" gcdC
 ]
 where thd (_, _, r) = r
       gcdC = thd <$> compileToC' "sgcd" (do
                cgSetDriverValues [55,154]
                x <- cgInput "x"
                y <- cgInput "y"
                cgReturn $ sgcd x y)
