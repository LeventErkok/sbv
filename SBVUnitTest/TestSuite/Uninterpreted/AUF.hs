-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.AUF
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.AUF where

import Data.SBV
import Data.SBV.Examples.Uninterpreted.AUF

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.AUF"
    [ testCase "auf-0" (assertIsThm (newArray "a" >>= \a -> free "x" >>= \x -> free "y" >>= \y -> free "i" >>= \i -> return (thm1 x y a i)))
    , testCase "auf-1" (assertIsThm (newArray "b" >>= \b -> free "x" >>= \x -> free "y" >>= \y                    -> return (thm2 x y b)))
    , goldenVsStringShow "auf-2" "auf-1.gold" pgm
    ]
 where pgm = runSAT $ do
                x <- free "x"
                y <- free "y"
                a <- newArray "a"
                i <- free "initVal"
                output $ thm1 x y a i
