-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CodeGeneration.CgTests
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for code-generation features
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.CodeGeneration.CgTests(testSuite) where

import Data.SBV
import Data.SBV.Internals

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "selChecked"   ~: genSelect True  "selChecked"   `goldCheck` "selChecked.gold"
 , "selUnchecked" ~: genSelect False "selUnChecked" `goldCheck` "selUnchecked.gold"
 , "codegen1"     ~: foo `goldCheck` "codeGen1.gold"
 ]
 where genSelect b n = compileToC' n $ do
                         cgSetDriverValues [65]
                         cgPerformRTCs b
                         let sel :: SWord8 -> SWord8
                             sel x = select [1, x+2] 3 x
                         x <- cgInput "x"
                         cgReturn $ sel x
       foo = compileToC' "foo" $ do
                        cgSetDriverValues $ repeat 0
                        (x::SInt16)    <- cgInput "x"
                        (ys::[SInt64]) <- cgInputArr 45 "xArr"
                        cgOutput "z" (5 :: SWord16)
                        cgOutputArr "zArr" (replicate 7 (x+1))
                        cgOutputArr "yArr" ys
                        cgReturn (x*2)
