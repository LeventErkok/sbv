-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Crypto.RC4
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Crypto.RC4
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Crypto.RC4(benchmarks) where

import Documentation.SBV.Examples.Crypto.RC4

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runIO "Correctness" rc4IsCorrect
  , runPure "encrypt 1" (concatMap hex2) $ encrypt "Key" "Plaintext"
  , runPure "encrypt 2" (concatMap hex2) $ encrypt "Wiki" "pedia"
  , runPure "encrypt 3" (concatMap hex2) $ encrypt "Secret" "Attack at dawn"
  , runPure "decrypt 1" (decrypt "Key")    [0xbb, 0xf3, 0x16, 0xe8, 0xd9, 0x40, 0xaf, 0x0a, 0xd3]
  , runPure "decrypt 2" (decrypt "Wiki")   [0x10, 0x21, 0xbf, 0x04, 0x20]
  , runPure "decrypt 3" (decrypt "Secret") [0x45, 0xa0, 0x1f, 0x64, 0x5f, 0xc3, 0x5b, 0x38, 0x35, 0x52, 0x54, 0x4b, 0x9b, 0xf5]
  ]
