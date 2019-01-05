-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Uninterpreted.AUF
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
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
    [ goldenVsStringShow "auf-0" $ runSAT      $ newArray "a" Nothing >>= \a -> free "x" >>= \x -> free "y" >>= \y -> output (thm x y (a :: SFunArray  Word32 Word32))
    , goldenVsStringShow "auf-1" $ runSAT      $ newArray "a" Nothing >>= \a -> free "x" >>= \x -> free "y" >>= \y -> output (thm x y (a :: SArray     Word32 Word32))
    , testCase "tc_auf-0"        $ assertIsThm $ newArray "a" Nothing >>= \a -> free "x" >>= \x -> free "y" >>= \y -> return (thm x y (a :: SArray     Word32 Word32))
    , testCase "tc_auf-1"        $ assertIsThm $ newArray "a" Nothing >>= \a -> free "x" >>= \x -> free "y" >>= \y -> return (thm x y (a :: SFunArray  Word32 Word32))
    ]
