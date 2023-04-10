-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.AllSat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for basic allsat calls
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.AllSat(tests) where

import Utils.SBVTestFramework

import Control.Monad(void)
import Data.List (sortOn)

import qualified Control.Exception as C

data Q
mkUninterpretedSort ''Q

tests :: TestTree
tests =
  testGroup "Basics.AllSat"
    [ goldenVsStringShow "allSat1" t1
    , goldenVsStringShow "allSat2" t2
    , goldenVsStringShow "allSat3" $            allSat $ \x -> x .== (0::SFloat)
    , goldenVsStringShow "allSat4" $            allSat $ \x -> x .<  (0::SWord8)
    , goldenVsStringShow "allSat5" $ fmap srt $ allSat $ \x y -> x .< y .&& y .< (4::SWord8)
    , goldenVsStringShow "allSat6" $            allSat t3
    , goldenCapturedIO   "allSat7" $ \rf -> void (allSatWith z3{verbose=True, redirectVerbose=Just rf} t4)
    , goldenCapturedIO   "allSat8" $ \rf -> void (allSatWith z3{verbose=True, redirectVerbose=Just rf} t5)
                                            `C.catch` (\(e :: C.SomeException) -> appendFile rf ("\nEXCEPTION CAUGHT:\n" ++ show e ++ "\n"))
    ]

srt :: AllSatResult -> AllSatResult
srt r@AllSatResult{allSatResults = ms} = r { allSatResults = sortOn (show . SatResult) ms }

t1 :: IO AllSatResult
t1 = allSat $ do x <- free "x"
                 y <- free "y"
                 return $ x .== (y :: SQ)

t2 :: IO AllSatResult
t2 = allSat $ do x <- free "x"
                 y <- free "y"
                 z <- free "z"
                 return $ x .== (y :: SQ) .&& z .== (z :: SQ)

t3 :: ConstraintSet
t3 = do x <- free "x"
        y <- free "y"
        constrain $ \(Forall z) -> x .< (y::SWord8) .&& y .< 3 .&& z .== (z::SWord8)

t4 :: ConstraintSet
t4 = do x <- sInteger "x"
        y <- sInteger "y"
        z <- sInteger "z"

        let range = (1, 15)

        constrain $ x `inRange` range
        constrain $ y `inRange` range
        constrain $ z `inRange` range

        constrain $ distinct [x, y, z]

t5 :: ConstraintSet
t5 = constrain $ \(Forall x) -> uninterpret "f" x .== x+(1::SInteger)
