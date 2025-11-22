-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.EUFLogic
-- License   : BSD3
-- Stability : experimental
--
-- Test suite for the EUFLogic example
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Uninterpreted.EUFLogic where

import Documentation.SBV.Examples.Uninterpreted.EUFLogic

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.EUFLogic"
    [ testCase  "euflogic-1" $ assertIsThm (interpEUF example)
    , testCase  "euflogic-2" $ assertIsThm (interpEUF fourteen)
    ]

fourteen :: EUFExpr Tp_Bool
fourteen =
  applyOp Op_And (applyOp (Op_BVEq knownBVWidth)
                          (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0
                          (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0 a))
                          (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0 a))
                 (applyOp Op_And (applyOp (Op_BVEq knownBVWidth)
                                          a
                                          (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0 b))
                                          (applyOp Op_Not
    (applyOp (Op_BVEq knownBVWidth) a b)))
  where
    f14 :: Op '[Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8,
                Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8]
           (Tp_BV 8)
    f14 = mkUnintOp "f"
    a :: EUFExpr (Tp_BV 8)
    a = mkUnintExpr "a"
    b :: EUFExpr (Tp_BV 8)
    b = mkUnintExpr "b"
