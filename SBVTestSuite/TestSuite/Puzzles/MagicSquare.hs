-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.MagicSquare
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.MagicSquare
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.MagicSquare(tests) where

import Documentation.SBV.Examples.Puzzles.MagicSquare

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Puzzles.MagicSquare"
    [ testCase "magic 2" (assertIsntSat (mkMagic 2))
    , testCase "magic 3" (assertIsSat (mkMagic 3))
    ]


mkMagic :: Int -> Symbolic SBool
mkMagic n = (isMagic . chunk n) `fmap` mkFreeVars (n*n)
