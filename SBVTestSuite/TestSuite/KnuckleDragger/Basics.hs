-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.KnuckleDragger.Basics
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for knuckle dragger
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.KnuckleDragger.Basics(tests) where

import Data.List(isPrefixOf)
import Utils.SBVTestFramework

import Documentation.SBV.Examples.KnuckleDragger.ShefferStroke

-- Test suite
tests :: TestTree
tests =
  testGroup "KnuckleDragger.Basics"
    [ silentlyCaptureIO "sheffer_stroke" (5000000, tag . clean) shefferBooleanAlgebra
    ]

-- Avoid the silently droppings.. Anything before we see "Axiom"
clean :: String -> String
clean s | null s = ""
        | "Axiom:" `isPrefixOf` s = s
        | True                    = clean (drop 1 s)

-- Tag, so that we can match what we put for doctest
tag :: String -> String
tag = unlines . map ("-- " ++) . lines
