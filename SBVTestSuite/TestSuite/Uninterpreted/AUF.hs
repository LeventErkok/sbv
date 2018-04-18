-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.AUF
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Documentation.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.AUF where

import Documentation.SBV.Examples.Uninterpreted.AUF

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.AUF"
    [ goldenVsStringShow "auf-1" pgm
    , testCase "auf-2" (assertIsThm (free "x" >>= \x -> free "y" >>= \y -> return (thm1 x y (mkSFunArray (const 0)))))
    , testCase "auf-3" (assertIsThm (newArray "b" >>= \b -> free "x" >>= \x -> free "y" >>= \y -> return (thm2 x y b)))
    ]
 where pgm = runSAT $ do
                x <- free "x"
                y <- free "y"
                output $ thm1 x y (mkSFunArray (const 0))
