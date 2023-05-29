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
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.UISat(tests)  where

import Data.SBV.Control
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.UIAllSat" [
      goldenCapturedIO "uiSat_test1" $ \rf -> checkWith rf test1
    , goldenCapturedIO "uiSat_test2" $ \rf -> checkWith rf test2
    , goldenCapturedIO "uiSat_test3" $ \rf -> checkWith rf test3
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
           registerUISMTFunction q1

test2 :: ConstraintSet
test2 = do setLogic Logic_ALL
           registerUISMTFunction q2

test3 :: ConstraintSet
test3 = do setLogic Logic_ALL
           registerUISMTFunction q1
           registerUISMTFunction q2

{- HLint ignore module "Reduce duplication" -}
