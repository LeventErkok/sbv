-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CodeGeneration.CgTests
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for code-generation features
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CodeGeneration.CgTests(testSuite) where

import Data.SBV
import Data.SBV.Internals

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "codegen1" ~: compileToC' [65] True  "selChecked"   [] sel `goldCheck` "selChecked.gold"
 , "codegen2" ~: compileToC' [65] False "selUnChecked" [] sel `goldCheck` "selUnchecked.gold"
 ]

sel :: SWord8 -> SWord8
sel x = select [1, x+2] 3 x
