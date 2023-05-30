-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.Quantified
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for optimization with quantifiers
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Optimization.Quantified(tests) where

import Data.List (isPrefixOf)

import Utils.SBVTestFramework
import qualified Control.Exception as C

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Reals"
    [ goldenVsStringShow "optQuant1" $ opt  q1
    , goldenVsStringShow "optQuant2" $ opt  q2
    , goldenVsStringShow "optQuant3" $ opt  q3
    , goldenVsStringShow "optQuant4" $ opt  q4
    , goldenString       "optQuant5" $ optE q5
    ]
    where opt    = optimize Lexicographic
          optE q = (show <$> optimize Lexicographic q) `C.catch` (\(e::C.SomeException) -> return (pick (show e)))
          pick s = unlines [l | l <- lines s, "***" `isPrefixOf` l]

q1 :: ConstraintSet
q1 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        constrain $ \(Forall x) ->     2 * (a * x + b1) .== 2
                                   .&& 4 * (a * x + b2) .== 4
        constrain $ a .>= 0
        minimize "goal" $ 2*a

q2 :: ConstraintSet
q2 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        constrain $ \(Forall x) ->     2 * (a * x + b1) .== 2
                                   .&& 4 * (a * x + b2) .== 4
                                   .&& a .>= 0
        minimize "goal" a

q3 :: ConstraintSet
q3 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        minimize "goal" a
        constrain $ \(Forall x) ->     2 * (a * x + b1) .== 2
                                   .&& 4 * (a * x + b2) .== 4
        constrain $ a .>= 0

q4 :: ConstraintSet
q4 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        minimize "goal" $ 2*a
        constrain $ \(Forall x) ->     2 * (a * x + b1) .== 2
                                   .&& 4 * (a * x + b2) .== 4
        constrain $ a .>= 0

q5 :: ConstraintSet
q5 = do a <- sInteger "a"
        constrain $ \(Exists y) -> a .>= (y :: SInteger)
        constrain $ a .>= 0
        b <- sInteger "b"
        constrain $ b .>= 0
        minimize "goal" $ a+b

{- HLint ignore module "Reduce duplication" -}
