-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.UISat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing UI function sat examples via queries
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.UISat(tests)  where

import Control.Monad (unless, when)

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Queries.UIAllSat" [
      goldenCapturedIO "query_uiSat_test1" $ \rf -> checkWith rf (mkCfg rf) test1 Sat
    , goldenCapturedIO "query_uiSat_test2" $ \rf -> checkWith rf (mkCfg rf) test2 Sat
    ]

mkCfg :: FilePath -> SMTConfig
mkCfg rf = z3 { verbose             = True
              , redirectVerbose     = Just rf
              , allSatMaxModelCount = Just 80
              , isNonModelVar       = (`elem` ["nx", "ny", "nz"])
              }

checkWith :: FilePath -> SMTConfig -> Symbolic () -> CheckSatResult -> IO ()
checkWith rf cfg props csExpected = runSMTWith cfg{verbose=True} $ do
        _ <- props
        query $ do cs <- checkSat
                   unless (cs == csExpected) $
                     case cs of
                       Unsat  -> error "Failed! Expected Sat, got UNSAT"
                       DSat{} -> error "Failed! Expected Sat, got delta-satisfiable!"
                       Sat    -> getModel         >>= \r -> error $ "Failed! Expected Unsat, got SAT:\n" ++ show (SatResult (Satisfiable cfg r))
                       Unk    -> getUnknownReason >>= \r -> error $ "Failed! Expected Unsat, got UNK:\n" ++ show r
                   when (cs == Sat) $
                       getModel >>= \m -> io $ appendFile rf $ "\nMODEL: " ++ show m ++ "\nDONE."

q1 :: SBool -> SBool
q1 = uninterpret "q1"

q2 :: SBool -> SBool -> SBool
q2 = uninterpret "q2"

test1 :: Symbolic ()
test1 = do setLogic Logic_ALL
           constrain $ q1 sFalse .== sFalse
           constrain $ q1 sTrue  .== sTrue

test2 :: Symbolic ()
test2 = do setLogic Logic_ALL
           constrain $ q2 sFalse sTrue  .== sFalse
           constrain $ q2 sTrue  sTrue  .== sTrue
           constrain $ q2 sTrue  sFalse .== sTrue
