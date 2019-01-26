-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.AddSub
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.CodeGeneration.AddSub
-----------------------------------------------------------------------------

module TestSuite.CodeGeneration.AddSub(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.CodeGeneration.AddSub

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CodeGen.addSub" [
   goldenVsStringShow "addSub" code
 ]
 where code = snd <$> compileToC' "addSub" (do
                cgSetDriverValues [76, 92]
                cgPerformRTCs True
                x <- cgInput "x"
                y <- cgInput "y"
                let (s, d) = addSub x y
                cgOutput "sum" s
                cgOutput "dif" d)
