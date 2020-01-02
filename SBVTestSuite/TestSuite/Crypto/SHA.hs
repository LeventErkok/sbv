-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Crypto.SHA
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Crypto.SHA
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Crypto.SHA(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.Crypto.SHA

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Crypto.AES" [
   goldenVsStringShow "sha256HashBlock" $ (\(_, _, r) -> r) <$> compileToC' "sha256HashBlock" c
 ]
 where c = do let algorithm = sha256P

              hInBytes   <- cgInputArr 32 "hIn"
              blockBytes <- cgInputArr 64 "block"

              let hIn   = chunkBy 4 fromBytes hInBytes
                  block = chunkBy 4 fromBytes blockBytes

                  result = hashBlock algorithm hIn (Block block)

              cgOutputArr "hash" $ concatMap toBytes result

              -- Use known test values for the empty string input so we get a meaningful driver
              let msgWords = concat [xs | Block xs <- prepareMessage algorithm "SBV goes SHA256!!"]
              cgShowU8UsingHex True
              cgSetDriverValues [fromIntegral x | Just x <- map unliteral (concatMap toBytes (h0 algorithm ++ msgWords))]
