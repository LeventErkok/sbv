-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.IteTest
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test various incarnations of ite/iteLazy/sBranch
-----------------------------------------------------------------------------

module TestSuite.Basics.IteTest(testSuite)  where

import Data.SBV
import Data.SBV.Internals

import SBVTest

chk1 :: (SBool -> SBool -> SBool -> SBool) -> SWord8 -> SBool
chk1 cond x = cond (x .== x) true undefined

chk2 :: (SBool -> [SBool] -> [SBool] -> [SBool]) -> SWord8 -> SBool
chk2 cond x = head (cond (x .== x) [true] [undefined])

chk3 :: (SBool -> (SBool, SBool) -> (SBool, SBool)  -> (SBool, SBool)) -> SWord8 -> SBool
chk3 cond x = fst (cond (x .== x) (true, undefined::SBool) (undefined, undefined))

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "ite-1"  ~: rs (chk1 ite) `goldCheck` "iteTest1.gold"
 , "ite-2"  ~: rs (chk2 ite) `goldCheck` "iteTest2.gold"
 , "ite-3"  ~: rs (chk3 ite) `goldCheck` "iteTest3.gold"
 , "ite-4"  ~: assert =<< isThm (chk1 iteLazy)
 , "ite-5"  ~: assert =<< isThm (chk2 iteLazy)
 , "ite-6"  ~: assert =<< isThm (chk3 iteLazy)
 , "ite-7"  ~: assert =<< isThm (chk1 sBranch)
 , "ite-8"  ~: assert =<< isThm (chk2 sBranch)
 , "ite-9"  ~: assert =<< isThm (chk3 sBranch)
 ]
 where rs f = runSymbolic (True, Nothing) $ forAll ["x"] f
