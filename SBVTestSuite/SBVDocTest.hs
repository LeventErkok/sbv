-----------------------------------------------------------------------------
-- |
-- Module    : SBVDocTest
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Doctest interface for SBV testsuite
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import System.Process
import System.Exit(exitWith)

main :: IO ()
main = exitWith =<< rawSystem "cabal-docspec" ["--timeout", "120"]
