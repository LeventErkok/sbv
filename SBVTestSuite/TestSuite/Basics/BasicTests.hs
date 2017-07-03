-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.BasicTests
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Basics.BasicTests
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Basics.BasicTests(tests) where

import Data.SBV.Internals
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Basics.BasicTests"
   [ testCase "basic-0.1" $ test0 f1 `showsAs` "5"
   , testCase "basic-0.2" $ test0 f2 `showsAs` "5"
   , testCase "basic-0.3" $ test0 f3 `showsAs` "25"
   , testCase "basic-0.4" $ test0 f4 `showsAs` "25"
   , testCase "basic-0.5" $ test0 f5 `showsAs` "4"
   , goldenVsStringShow "basic-1_1" $ test1 f1
   , goldenVsStringShow "basic-1_2" $ test1 f2
   , goldenVsStringShow "basic-1_3" $ test1 f3
   , goldenVsStringShow "basic-1_4" $ test1 f4
   , goldenVsStringShow "basic-1_5" $ test1 f5
   , goldenVsStringShow "basic-2_1" $ test2 f1
   , goldenVsStringShow "basic-2_2" $ test2 f2
   , goldenVsStringShow "basic-2_3" $ test2 f3
   , goldenVsStringShow "basic-2_4" $ test2 f4
   , goldenVsStringShow "basic-2_5" $ test2 f5
   , goldenVsStringShow "basic-3_1" $ test3 f1
   , goldenVsStringShow "basic-3_2" $ test3 f2
   , goldenVsStringShow "basic-3_3" $ test3 f3
   , goldenVsStringShow "basic-3_4" $ test3 f4
   , goldenVsStringShow "basic-3_5" $ test3 f5
   , goldenVsStringShow "basic-4_1" $ test4 f1
   , goldenVsStringShow "basic-4_2" $ test4 f2
   , goldenVsStringShow "basic-4_3" $ test4 f3
   , goldenVsStringShow "basic-4_4" $ test4 f4
   , goldenVsStringShow "basic-4_5" $ test4 f5
   , goldenVsStringShow "basic-5_1" $ test5 f1
   , goldenVsStringShow "basic-5_2" $ test5 f2
   , goldenVsStringShow "basic-5_3" $ test5 f3
   , goldenVsStringShow "basic-5_4" $ test5 f4
   , goldenVsStringShow "basic-5_5" $ test5 f5
   ]

test0 :: (forall a. Num a => (a -> a -> a)) -> Word8
test0 f = f (3 :: Word8) 2

test1, test2, test3, test4, test5 :: (forall a. Num a => (a -> a -> a)) -> IO Result
test1 f = runSAT $ do let x = literal (3 :: Word8)
                          y = literal (2 :: Word8)
                      output $ f x y
test2 f = runSAT $ do let x = literal (3 :: Word8)
                      y :: SWord8 <- forall "y"
                      output $ f x y
test3 f = runSAT $ do x :: SWord8 <- forall "x"
                      y :: SWord8 <- forall "y"
                      output $ f x y
test4 f = runSAT $ do x :: SWord8 <- forall "x"
                      output $ f x x
test5 f = runSAT $ do x :: SWord8 <- forall "x"
                      let r = f x x
                      q :: SWord8 <- forall "q"
                      _ <- output q
                      output r

f1, f2, f3, f4, f5 :: Num a => a -> a -> a
f1 x y = (x+y)*(x-y)
f2 x y = (x*x)-(y*y)
f3 x y = (x+y)*(x+y)
f4 x y = let z = x + y in z * z
f5 x _ = x + 1
