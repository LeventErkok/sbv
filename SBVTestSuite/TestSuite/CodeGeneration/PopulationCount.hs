-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.PopulationCount
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.CodeGeneration.PopulationCount
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.PopulationCount(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.CodeGeneration.PopulationCount

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CodeGeneration.PopulationCount" [
   goldenVsStringShow "popCount1" $ thd <$> genC False
 , goldenVsStringShow "popCount2" $ thd <$> genC True
 ]
 where genC b = compileToC' "popCount" $ do
                  cgSetDriverValues [0x0123456789ABCDEF]
                  cgPerformRTCs b
                  x <- cgInput "x"
                  cgReturn $ popCountFast x
       thd (_, _, r) = r
