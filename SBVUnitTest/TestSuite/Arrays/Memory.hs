-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Arrays.Memory
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Arrays.Memory
-----------------------------------------------------------------------------

module TestSuite.Arrays.Memory(testSuite) where

import Examples.Arrays.Memory
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
     "memory-raw"           ~: assert       =<< isThm t1
   , "memory-waw"           ~: assert       =<< isThm t2
   , "memory-wcommute-good" ~: assert       =<< isThm t3
   , "memory-wcommute-bad"  ~: assert . not =<< isThm t4
   ]
   where t1 = free "a" >>= \a -> free "x" >>= \x ->                                       newArray "m" Nothing >>= return . raw a x
         t2 = free "a" >>= \a -> free "x" >>= \x -> free "y" >>= \y ->                    newArray "m" Nothing >>= return . waw a x y
         t3 = free "a" >>= \a -> free "x" >>= \x -> free "b" >>= \b -> free "y" >>= \y -> newArray "m" Nothing >>= return . wcommutesGood (a, x) (b, y)
         t4 = free "a" >>= \a -> free "x" >>= \x -> free "b" >>= \b -> free "y" >>= \y -> newArray "m" Nothing >>= return . wcommutesBad  (a, x) (b, y)

{-# ANN module ("HLint: ignore Use fmap" :: String) #-}
