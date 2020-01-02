-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.CgTests
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for code-generation features
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.CgTests(tests) where

import Data.SBV.Internals

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CodeGeneration.CgTests" [
   goldenVsStringShow "selChecked"   $ genSelect True  "selChecked"
 , goldenVsStringShow "selUnchecked" $ genSelect False "selUnChecked"
 , goldenVsStringShow "codeGen1"       foo
 ]
 where thd (_, _, r) = r

       genSelect b n = thd <$> compileToC' n (do
                         cgSetDriverValues [65]
                         cgPerformRTCs b
                         let sel :: SWord8 -> SWord8
                             sel x = select [1, x+2] 3 x
                         x <- cgInput "x"
                         cgReturn $ sel x)
       foo = thd <$> compileToC' "foo" (do
                        cgSetDriverValues $ repeat 0
                        (x::SInt16)    <- cgInput "x"
                        (ys::[SInt64]) <- cgInputArr 45 "xArr"
                        cgOutput "z" (5 :: SWord16)
                        cgOutputArr "zArr" (replicate 7 (x+1))
                        cgOutputArr "yArr" ys
                        cgReturn (x*2))
