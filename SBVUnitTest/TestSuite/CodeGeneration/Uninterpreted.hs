-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CodeGeneration.Uninterpreted
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.CodeGeneration.Uninterpreted
-----------------------------------------------------------------------------
module TestSuite.CodeGeneration.Uninterpreted(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.Uninterpreted

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "cgUninterpret" ~: genC `goldCheck` "cgUninterpret.gold"
 ]
 where genC = compileToC' "tstShiftLeft" $ do
                  cgSetDriverValues [1, 2, 3]
                  [x, y, z] <- cgInputArr 3 "vs"
                  cgReturn $ tstShiftLeft x y z
