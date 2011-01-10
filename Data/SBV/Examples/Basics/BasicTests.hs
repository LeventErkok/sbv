-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Basics.BasicTests
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Basic tests of the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.Basics.BasicTests where

import Data.SBV
import Data.SBV.Utils.SBVTest

test0 :: (forall a. Num a => (a -> a -> a)) -> Word8
test0 f = f (3 :: Word8) 2

test1, test2, test3, test4, test5 :: (forall a. Num a => (a -> a -> a)) -> IO Result
test1 f = runSymbolic $ do let x = literal (3 :: Word8)
                               y = literal (2 :: Word8)
                           output $ f x y
test2 f = runSymbolic $ do let x = literal (3 :: Word8)
                           y :: SWord8 <- free "y"
                           output $ f x y
test3 f = runSymbolic $ do x :: SWord8 <- free "x"
                           y :: SWord8 <- free "y"
                           output $ f x y
test4 f = runSymbolic $ do x :: SWord8 <- free "x"
                           output $ f x x
test5 f = runSymbolic $ do x :: SWord8 <- free "x"
                           let r = f x x
                           q :: SWord8 <- free "q"
                           _ <- output q
                           output r

f1, f2, f3, f4, f5 :: Num a => a -> a -> a
f1 x y = (x+y)*(x-y)
f2 x y = (x*x)-(y*y)
f3 x y = (x+y)*(x+y)
f4 x y = let z = x + y in z * z
f5 x _ = x + 1

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "basic-0.1" ~: test0 f1 `showsAs` "5"
 , "basic-0.2" ~: test0 f2 `showsAs` "5"
 , "basic-0.3" ~: test0 f3 `showsAs` "25"
 , "basic-0.4" ~: test0 f4 `showsAs` "25"
 , "basic-0.5" ~: test0 f5 `showsAs` "4"
 , "basic-1.1" ~: test1 f1 `goldCheck` "basic-1_1.gold"
 , "basic-1.2" ~: test1 f2 `goldCheck` "basic-1_2.gold"
 , "basic-1.3" ~: test1 f3 `goldCheck` "basic-1_3.gold"
 , "basic-1.4" ~: test1 f4 `goldCheck` "basic-1_4.gold"
 , "basic-1.5" ~: test1 f5 `goldCheck` "basic-1_5.gold"
 , "basic-2.1" ~: test2 f1 `goldCheck` "basic-2_1.gold"
 , "basic-2.2" ~: test2 f2 `goldCheck` "basic-2_2.gold"
 , "basic-2.3" ~: test2 f3 `goldCheck` "basic-2_3.gold"
 , "basic-2.4" ~: test2 f4 `goldCheck` "basic-2_4.gold"
 , "basic-2.5" ~: test2 f5 `goldCheck` "basic-2_5.gold"
 , "basic-3.1" ~: test3 f1 `goldCheck` "basic-3_1.gold"
 , "basic-3.2" ~: test3 f2 `goldCheck` "basic-3_2.gold"
 , "basic-3.3" ~: test3 f3 `goldCheck` "basic-3_3.gold"
 , "basic-3.4" ~: test3 f4 `goldCheck` "basic-3_4.gold"
 , "basic-3.5" ~: test3 f5 `goldCheck` "basic-3_5.gold"
 , "basic-4.1" ~: test4 f1 `goldCheck` "basic-4_1.gold"
 , "basic-4.2" ~: test4 f2 `goldCheck` "basic-4_2.gold"
 , "basic-4.3" ~: test4 f3 `goldCheck` "basic-4_3.gold"
 , "basic-4.4" ~: test4 f4 `goldCheck` "basic-4_4.gold"
 , "basic-4.5" ~: test4 f5 `goldCheck` "basic-4_5.gold"
 , "basic-5.1" ~: test5 f1 `goldCheck` "basic-5_1.gold"
 , "basic-5.2" ~: test5 f2 `goldCheck` "basic-5_2.gold"
 , "basic-5.3" ~: test5 f3 `goldCheck` "basic-5_3.gold"
 , "basic-5.4" ~: test5 f4 `goldCheck` "basic-5_4.gold"
 , "basic-5.5" ~: test5 f5 `goldCheck` "basic-5_5.gold"
 ]
