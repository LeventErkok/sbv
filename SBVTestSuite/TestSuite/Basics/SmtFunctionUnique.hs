-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.SmtFunctionUnique
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Tests for smtFunction name uniqueness enforcement.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.SmtFunctionUnique(tests) where

import Utils.SBVTestFramework

import qualified Control.Exception as C

-- Test suite
tests :: TestTree
tests = testGroup "Basics.SmtFunctionUnique"
   [
   -- Same name, same body: should succeed (idempotent re-registration).
     goldenCapturedIO "smtFuncUniq_sameOk" $ \rf -> do
        let f :: SInteger -> SInteger
            f = smtFunction "f" $ \x -> x + 1
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> f x + f x .== 4
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Same name, different body: should error.
   , goldenCapturedIO "smtFuncUniq_conflict" $ \rf -> do
        let f :: SInteger -> SInteger
            f = smtFunction "f" $ \x -> x + 1
            g :: SInteger -> SInteger
            g = smtFunction "f" $ \x -> x + 2
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> f x + g x .== 5
        case r of
          Left (e :: C.SomeException) -> appendFile rf (show e ++ "\n")
          Right m                     -> appendFile rf ("\nUNEXPECTED SUCCESS:\n" ++ show m ++ "\n")

   -- Same name, same recursive body: should succeed.
   , goldenCapturedIO "smtFuncUniq_recursiveOk" $ \rf -> do
        let f :: SInteger -> SInteger
            f = smtFunction "f" $ \x -> ite (x .<= 0) 0 (x + f (x - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> x .>= 0 .&& x .<= 3 .&& f x .== 6
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Same name, different recursive body: should error.
   , goldenCapturedIO "smtFuncUniq_recursiveConflict" $ \rf -> do
        let f :: SInteger -> SInteger
            f = smtFunction "f" $ \x -> ite (x .<= 0) 0 (x + f (x - 1))
            g :: SInteger -> SInteger
            g = smtFunction "f" $ \x -> ite (x .<= 0) 1 (x * g (x - 1))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> f x + g x .== 10
        case r of
          Left (e :: C.SomeException) -> appendFile rf (show e ++ "\n")
          Right m                     -> appendFile rf ("\nUNEXPECTED SUCCESS:\n" ++ show m ++ "\n")

   -- Same name via parameter capture: bar 2 and bar 3 create different closures
   -- for "bar", which should be detected as a conflict.
   , goldenCapturedIO "smtFuncUniq_captureConflict" $ \rf -> do
        let bar :: SInteger -> SInteger -> SInteger
            bar k = smtFunction "bar" (+ k)
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> bar 2 x + bar 3 x .== 10
        case r of
          Left (e :: C.SomeException) -> appendFile rf (show e ++ "\n")
          Right m                     -> appendFile rf ("\nUNEXPECTED SUCCESS:\n" ++ show m ++ "\n")

   -- Fix for the above: use a tag to give each instantiation a unique name.
   , goldenCapturedIO "smtFuncUniq_captureTagged" $ \rf -> do
        let bar :: String -> SInteger -> SInteger -> SInteger
            bar tag k = smtFunction ("bar_" ++ tag) (+ k)
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> bar "two" 2 x + bar "three" 3 x .== 10
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")
   ]
