-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.Uninterpreted
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.CodeGeneration.Uninterpreted
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.Uninterpreted(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.CodeGeneration.Uninterpreted

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CodeGeneration.Uninterpreted" [
   goldenVsStringShow "cgUninterpret"  genC
 ]
 where genC = thd <$> compileToC' "tstShiftLeft" (do cgSetDriverValues [1, 2, 3]
                                                     [x, y, z] <- cgInputArr 3 "vs"
                                                     cgReturn $ tstShiftLeft x y z)
       thd (_, _, r) = r
