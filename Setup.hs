-----------------------------------------------------------------------------
-- |
-- Module    : Setup
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Setup module for the sbv library
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Main(main) where

import Distribution.Simple

main :: IO ()
main = defaultMain
