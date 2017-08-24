-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Optimization.Quantified
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for optimization iwth quantifiers
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Optimization.Quantified(tests) where

import Data.List (isPrefixOf)

import Utils.SBVTestFramework
import qualified Control.Exception as C

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Reals"
    [ goldenString       "optQuant1" ((show <$> optimize Lexicographic q1) `C.catch` (\(e::C.SomeException) -> return (pick (show e))))
    , goldenVsStringShow "optQuant2" (optimize Lexicographic q2)
    , goldenVsStringShow "optQuant3" (optimize Lexicographic q3)
    , goldenVsStringShow "optQuant4" (optimize Lexicographic q4)
    ]
    where pick s = unlines [l | l <- lines s, "***" `isPrefixOf` l]

q1 :: Goal
q1 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        x <- forall "x" :: Symbolic SInteger
        constrain $ 2 * (a * x + b1) .== 2
        constrain $ 4 * (a * x + b2) .== 4
        constrain $ a .>= 0
        minimize "goal" $ 2*x

q2 :: Goal
q2 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        x <- forall "x" :: Symbolic SInteger
        constrain $ 2 * (a * x + b1) .== 2
        constrain $ 4 * (a * x + b2) .== 4
        constrain $ a .>= 0
        minimize "goal" $ a

q3 :: Goal
q3 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        minimize "goal" $ a
        x <- forall "x" :: Symbolic SInteger
        constrain $ 2 * (a * x + b1) .== 2
        constrain $ 4 * (a * x + b2) .== 4
        constrain $ a .>= 0

q4 :: Goal
q4 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        minimize "goal" $ 2*a
        x <- forall "x" :: Symbolic SInteger
        constrain $ 2 * (a * x + b1) .== 2
        constrain $ 4 * (a * x + b2) .== 4
        constrain $ a .>= 0
