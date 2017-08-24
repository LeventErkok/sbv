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
    [ goldenString       "optQuant1" $ optE q1
    , goldenVsStringShow "optQuant2" $ opt  q2
    , goldenVsStringShow "optQuant3" $ opt  q3
    , goldenVsStringShow "optQuant4" $ opt  q4
    , goldenString       "optQuant5" $ optE q5
    ]
    where opt    = optimize Lexicographic
          optE q = (show <$> optimize Lexicographic q) `C.catch` (\(e::C.SomeException) -> return (pick (show e)))
          pick s = unlines [l | l <- lines s, "***" `isPrefixOf` l]

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
        minimize "goal" a

q3 :: Goal
q3 = do a <- sInteger "a"
        [b1, b2] <- sIntegers ["b1", "b2"]
        minimize "goal" a
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

q5 :: Goal
q5 = do a <- sInteger "a"
        x <- forall "x" :: Symbolic SInteger
        y <- forall "y" :: Symbolic SInteger
        b <- sInteger "b"
        constrain $ a .>= 0
        constrain $ b .>= 0
        constrain $ x+y .>= 0
        minimize "goal" $ a+b

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
