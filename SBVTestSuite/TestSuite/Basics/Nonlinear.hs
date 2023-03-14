-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Nonlinear
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some nonlinear tests, z3 and CVC5
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Nonlinear (tests)  where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Nonlinear" [
          goldenCapturedIO "nonlinear_z3"   $ check z3
        , goldenCapturedIO "nonlinear_cvc4" $ check cvc4
        , goldenCapturedIO "nonlinear_cvc5" $ check cvc5
        ]
    where check s gf = do r <- satWith s{verbose = True, redirectVerbose = Just gf} f
                          appendFile gf ("\nFINAL:\n" ++ show r ++ "\nDONE!\n")

          f :: SReal -> SBool
          f x = x * x .== 2
