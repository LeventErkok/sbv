-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.UISatEx
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing uninterpreted function extraction
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

#if MIN_VERSION_base(4,19,0)
{-# LANGUAGE TypeAbstractions    #-}
#endif

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.UISatEx where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Queries.UISatEx"
    [ goldenCapturedIO "query_uisatex1" testQuery1
    , goldenCapturedIO "query_uisatex2" testQuery2
    , goldenCapturedIO "query_uisatex3" testQuery3
    ]

testQuery1 :: FilePath -> IO ()
testQuery1 rf = do r <- satWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} core
                   appendFile rf ("\n FINAL:\n" ++ show r ++ "\nDONE!\n")

testQuery2 :: FilePath -> IO ()
testQuery2 rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf, allSatMaxModelCount = Just 5} qCore
                   appendFile rf ("\n FINAL:\n" ++ show r ++ "\nDONE!\n")
  where qCore = do core
                   let q6 :: SInteger -> SBool
                       q6 = uninterpret "q6"
                   constrain $ q6 0 .=> q6 0
                   query $ do registerUISMTFunction q6 -- Not really necessary, but testing it doesn't break anything
                              ensureSat
                              qv1 <- getFunction q1
                              qv2 <- getFunction q2
                              qv3 <- getFunction q3
                              qv4 <- getFunction q4
                              qv5 <- getFunction q5
                              qv6 <- getFunction q6
                              return (qv1, qv2, qv3, qv4, qv5, qv6)

q1 :: SInteger -> SInteger
q1 = uninterpret "q1"

q2 :: SBool -> SInteger -> SInteger
q2 = uninterpret "q2"

q3 :: SFloat -> SBool -> SInteger -> SFloat
q3 = uninterpret "q3"

q4 :: SChar -> SString -> SFloat
q4 = uninterpret "q4"

q5 :: SList Integer -> SList Float -> SInteger
q5 = uninterpret "q5"

core :: ConstraintSet
core = do x <- sInteger_
          constrain $ q1 2    .== 12
          constrain $ q1 3    .== 75
          constrain $ q1 (-3) .== 9
          constrain $ q1 x    .== x+1

          registerUISMTFunction q2 -- Not really necessary, but testing it doesn't break anything
          constrain $ q2 sTrue 3   .== 5
          constrain $ q2 sFalse 7  .== 6
          constrain $ q2 sFalse 12 .== 3

          constrain $                    q3 8.6 sTrue  12  .== 8.6
          constrain $ fpIsNegativeZero $ q3 9.6 sTrue  121
          constrain $                    q3 9.6 sFalse 8   .== 1/0

          constrain $ q4 (literal 'c') "hey" .== 78
          constrain $ q4 (literal 'c') "tey" .== 92
          constrain $ q4 (literal 'r') "foo" .== 3.5

          constrain $ q5 [1,2,3] [8.2, 3] .== 7
          constrain $ q5 [9,5]   [8.2, 9] .== 21
          constrain $ q5 [5]     [8.2, 0] .== 210

testQuery3 :: FilePath -> IO ()
testQuery3 rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                   appendFile rf ("\n FINAL:\n" ++ show r ++ "\nDONE!\n")

  where t = do constrain $ skolemize $ \(Forall @"x" x) (Exists @"y" y) -> y .== 3*(x::SInteger)
               query $ do cs <- checkSat
                          case cs of
                            Sat -> do yv <- getFunction (uninterpret "y" :: SInteger -> SInteger)
                                      case yv of
                                        Left x -> pure x
                                        _      -> error $ "Expected fundef, got: " ++ show yv
                            _   -> error $ "Expected sat, got: " ++ show cs

-- HLint complains about TypeApplications pragma, but if I remove it GHC complains
-- I'm not sure who is right here; so ignore.
{- HLint ignore module "Unused LANGUAGE pragma" -}
