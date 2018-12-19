-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Transformers.SymbolicEval
-- Copyright   :  (c) Brian Schroeder
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Documentation.SBV.Examples.Transformers.SymbolicEval
-----------------------------------------------------------------------------

module TestSuite.Transformers.SymbolicEval(tests) where

import Documentation.SBV.Examples.Transformers.SymbolicEval

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Transformers.SymbolicEval"
    [ testCase "counterexample" $ assert $ (== Right (Counterexample 0 9)) <$> ex1
    , testCase "proof"          $ assert $ (== Right Proved) <$> ex2
    , testCase "failure"        $ assert $ (== Left "unknown variable") <$> ex3
    ]
