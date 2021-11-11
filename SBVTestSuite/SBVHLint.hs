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

import Language.Haskell.HLint (hlint)
import System.Exit (exitFailure, exitSuccess)

arguments :: [String]
arguments =
    [ "Data"
    , "SBVTestSuite"
    , "-i", "Use otherwise"
    , "-i", "Parse error"
    , "--cpp-simple"
    ]

main :: IO ()
main = do hints <- hlint arguments
          if null hints
             then exitSuccess
             else exitFailure
