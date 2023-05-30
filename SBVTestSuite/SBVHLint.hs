-----------------------------------------------------------------------------
-- |
-- Module    : SBVHLint
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- HLint interface for SBV testsuite
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Main (main) where

import System.Exit (exitWith)
import System.Process

arguments :: [String]
arguments =
    [ "Data"
    , "SBVTestSuite"
    , "Documentation"
    , "-i", "Use otherwise"
    , "-i", "Parse error"
    , "--cpp-simple"
    ]

main :: IO ()
main = exitWith =<< rawSystem "hlint" arguments
