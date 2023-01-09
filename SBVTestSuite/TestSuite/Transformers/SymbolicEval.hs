-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Transformers.SymbolicEval
-- Copyright : (c) Brian Schroeder
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Transformers.SymbolicEval
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Transformers.SymbolicEval(tests) where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Data.Either          (isLeft)

import Data.SBV.Trans         (runSMT, sat)
import Data.SBV.Trans.Control (query)

import Documentation.SBV.Examples.Transformers.SymbolicEval
import Utils.SBVTestFramework                               hiding (runSMT, sat)

isSat :: SatResult -> Bool
isSat (SatResult Unsatisfiable{}) = False
isSat (SatResult Satisfiable{})   = True
isSat _                           = error "isSat: Unexpected result!"

-- Test suite
tests :: TestTree
tests = testGroup "Transformers.SymbolicEval"
    [ testCase "tse_alloc_success" $ assert $
          (== Right True) . fmap isSat <$>
            runExceptT (sat $ (.< 5) <$> runAlloc (alloc "x") :: ExceptT String IO SatResult)

    , testCase "tse_alloc_failure" $ assert $
          (== Left "tried to allocate unnamed value") <$>
              runExceptT (runSMT (runAlloc (alloc "")))

    , testCase "tse_query_success" $ assert $
          (== Right (Just True)) . fmap unliteral <$>
              runExceptT (runSMT (query (runQ (pure $ (5 :: SInt8) .< 6))))

    , testCase "tse_query_failure" $ assert $
          isLeft <$>
              runExceptT (runSMT (query (runQ $ throwError "oops")))

    , testCase "tse_combined_success" $ assert $
          (== Right (Counterexample 0 9)) <$>
              check (Program  $ Var "x" `Plus` Lit 1 `Plus` Var "y")
                    (Property $ Var "result" `LessThan` Lit 10)

    , testCase "tse_combined_failure" $ assert $
          (== Left "unknown variable") <$>
              check (Program  $ Var "notAValidVar")
                    (Property $ Var "result" `LessThan` Lit 10)
    ]
