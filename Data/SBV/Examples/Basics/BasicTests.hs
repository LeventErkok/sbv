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
import Data.SBV.Internals

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
