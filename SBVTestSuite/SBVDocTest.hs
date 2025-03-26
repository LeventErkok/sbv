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

import System.Environment(getArgs)
import System.Exit(exitWith)

import System.Process

-- This "fake" import creates a dependency to sbv,
-- thus allowing cabal to recognize it has to compile
-- sbv first before running the doctests. Otherwise it plays no role.
import Data.SBV ()

main :: IO ()
main = do args <- getArgs
          exitWith =<< rawSystem "cabal-docspec" args
