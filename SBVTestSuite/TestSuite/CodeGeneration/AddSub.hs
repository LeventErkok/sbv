-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CodeGeneration.AddSub
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.CodeGeneration.AddSub
-----------------------------------------------------------------------------

module TestSuite.CodeGeneration.AddSub(tests) where

import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.AddSub

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CodeGen.addSub" [
   goldenVsStringShow "addSub" code
 ]
 where code = compileToC' "addSub" $ do
                cgSetDriverValues [76, 92]
                cgPerformRTCs True
                x <- cgInput "x"
                y <- cgInput "y"
                let (s, d) = addSub x y
                cgOutput "sum" s
                cgOutput "dif" d
