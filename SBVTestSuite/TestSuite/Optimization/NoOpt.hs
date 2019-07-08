-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.NoOpt
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Check that if optimization is done, there must be goals and vice versa
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Optimization.NoOpt(tests) where

import qualified Control.Exception as C

import Control.Monad (void)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.NoOpt"
       [ goldenCapturedIO "noOpt1" $ \rf -> c rf $ optimizeWith z3{verbose=True, redirectVerbose=Just rf} Lexicographic (\x -> x .== (x::SWord8))
       , goldenCapturedIO "noOpt2" $ \rf -> c rf $ satWith      z3{verbose=True, redirectVerbose=Just rf}               (\x -> maximize "mx" (x::SWord8))
       ]
 where -- catch the exception and put it in the file. Note that we trim the last line since it contains the
       -- cabal hash of the library, which is bound to change
       c rf cont = void cont `C.catch` (\(e :: C.SomeException) -> appendFile rf ("\n\n" ++ unlines (init (lines (show e))) ++ "\n"))
