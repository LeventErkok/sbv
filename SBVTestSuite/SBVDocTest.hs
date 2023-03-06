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

main :: IO ()
main = do args <- getArgs
          exitWith =<< rawSystem "cabal-docspec" args
