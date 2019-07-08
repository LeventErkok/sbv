-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Assert
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the sAssert feature.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Assert(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Assert"
   [ goldenCapturedIO "safe1" $ t $ \x -> sAssert Nothing "safe1" (x .> (2::SInteger)) (x .== 12)
   , goldenCapturedIO "safe2" $ t $ \x -> sAssert Nothing "safe2" (x .> (2::SInteger)) (12::SInteger)
   ]
   where t tc goldFile = do r <- safeWith z3{verbose=True, redirectVerbose=Just goldFile} tc
                            appendFile goldFile ("\n FINAL: " ++ show r ++ "\nDONE!")
