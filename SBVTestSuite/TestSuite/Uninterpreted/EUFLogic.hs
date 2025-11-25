-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.EUFLogic
-- License   : BSD3
-- Stability : experimental
--
-- Test suite for the EUFLogic example
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Uninterpreted.EUFLogic where

import Documentation.SBV.Examples.Uninterpreted.EUFLogic

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.LargeArgs"
    [ testCase "euflogic-1" $ assertIsSat (interpEUF fourteen)
    , testCase "unint17arg" $ assertIsSat f17Args
    ]

fourteen :: EUFExpr Tp_Bool
fourteen = applyOp (Op_BVEq knownBVWidth)
                   (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                   (applyOp (Op_Plus knownBVWidth) a b)
  where
    f14 :: Op '[Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8,
                Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8]
           (Tp_BV 8)

    f14 = mkUnintOp "f"
    a, b :: EUFExpr (Tp_BV 8)
    a = mkUnintExpr "a"
    b = mkUnintExpr "b"

f17Args :: SWord  1 -> SWord  2 -> SWord  3 -> SWord  4 -> SWord  5 -> SWord  6 -> SWord  7 -> SWord 8
        -> SWord  9 -> SWord 10 -> SWord 11 -> SWord 12 -> SWord 13 -> SWord 14 -> SWord 15 -> SWord 16
        -> SWord 17
        -> SBool
f17Args = uninterpret "f17Args"

{- HLint ignore "Use camelCase" -}
