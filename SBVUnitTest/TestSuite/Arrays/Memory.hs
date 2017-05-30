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

module TestSuite.Arrays.Memory(tests) where

import Examples.Arrays.Memory (raw, waw, wcommutesGood, wcommutesBad)
import SBVTest

tests :: TestTree
tests =
  testGroup "Arrays.Memory"
    [ testCase "raw"
        (assertIsThm
          (free "a" >>= \a -> free "x" >>= \x ->                                       newArray "m" Nothing >>= return . raw a x))
    , testCase "waw"
        (assertIsThm
          (free "a" >>= \a -> free "x" >>= \x -> free "y" >>= \y ->                    newArray "m" Nothing >>= return . waw a x y))
    , testCase "wcommute-good"
        (assertIsThm
          (free "a" >>= \a -> free "x" >>= \x -> free "b" >>= \b -> free "y" >>= \y -> newArray "m" Nothing >>= return . wcommutesGood (a, x) (b, y)))
    , testCase "wcommute-bad"
        (assertIsntThm
          (free "a" >>= \a -> free "x" >>= \x -> free "b" >>= \b -> free "y" >>= \y -> newArray "m" Nothing >>= return . wcommutesBad  (a, x) (b, y)))
    ]

{-# ANN module ("HLint: ignore Use fmap" :: String) #-}
