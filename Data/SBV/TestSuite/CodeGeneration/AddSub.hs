-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CodeGeneration.AddSub
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CodeGeneration.AddSub
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CodeGeneration.AddSub(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.AddSub

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "addSub" ~: compileToC' [76, 92] True "addSub" ["x", "y", "sum", "dif"] addSub `goldCheck` "addSub.gold"
 ]
