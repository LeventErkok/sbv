-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.UISat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing UI function sat examples
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.UISat(tests)  where

import Utils.SBVTestFramework

import Data.SBV.Control

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.UIAllSat" [
      goldenCapturedIO "uiSat_test1" $ \rf -> checkWith rf test1
    , goldenCapturedIO "uiSat_test2" $ \rf -> checkWith rf test2
    , goldenCapturedIO "uiSat_test3" $ \rf -> checkWith rf test3
    , testCase "register_float_nan" $ assertIsSat $ do
        let f = uninterpret "nanFloat" :: SInteger -> SFloat
        constrain $ \(Forall x) -> fpIsNaN (f x)
        registerFunction f
        pure sTrue
    , testCase "register_double_nan" $ assertIsSat $ do
        let f = uninterpret "nanDouble" :: SInteger -> SDouble
        constrain $ \(Forall x) -> fpIsNaN (f x)
        registerFunction f
        pure sTrue
    , testCase "register_sized_float_nan" $ assertIsSat $ do
        let f = uninterpret "nanHalf" :: SInteger -> SFPHalf
        constrain $ \(Forall x) -> fpIsNaN (f x)
        registerFunction f
        pure sTrue
    , testCase "register_defined_nan" $ assertIsSat $ do
        let f = smtFunction "definedNaN" $ \(_ :: SInteger) -> (sNaN :: SFloat)
        registerFunction f
        pure sTrue
    , testCase "register_nan_literal" $ assertIsSat $ do
        registerFunction (sNaN :: SFloat)
        pure sTrue
    , testCase "register_unused_binary_function_model" $ do
        result <- runSMT $ do
          registerFunction q2
          query $ do ensureSat
                     getFunction q2
        case result of
          Right{} -> pure ()
          Left{}  -> assertFailure "Expected a binary Boolean function interpretation"
    ]

cfg :: FilePath -> SMTConfig
cfg rf = z3 { verbose             = True
            , redirectVerbose     = Just rf
            , allSatMaxModelCount = Just 80
            , isNonModelVar       = (`elem` ["nx", "ny", "nz"])
            }

checkWith :: FilePath -> ConstraintSet -> IO ()
checkWith rf prop = do r <- allSatWith (cfg rf) prop
                       appendFile rf $ "\nRESULT: " ++ show r

q1 :: SBool -> SBool
q1 = uninterpret "q1"

q2 :: SBool -> SBool -> SBool
q2 = uninterpret "q2"

test1 :: ConstraintSet
test1 = do setLogic Logic_ALL
           registerFunction q1

test2 :: ConstraintSet
test2 = do setLogic Logic_ALL
           registerFunction q2

test3 :: ConstraintSet
test3 = do setLogic Logic_ALL
           registerFunction q1
           registerFunction q2

{- HLint ignore module "Reduce duplication" -}
