-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.EUFLogic
-- License   : BSD3
-- Stability : experimental
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Uninterpreted.EUFLogic where

import Documentation.SBV.Examples.Uninterpreted.EUFLogic

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.EUFLogic"
    [ testCase         "euflogic-1"       $ assertIsThm (interpEUF example1)
    , testCase         "euflogic-2"       $ assertIsThm (interpEUF example2)
    ]
