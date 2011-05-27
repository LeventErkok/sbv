-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Crypto.RC4
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Crypto.RC4
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Crypto.RC4(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Crypto.RC4

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "rc4swap" ~: assert =<< isTheorem swapIsCorrect
 ]
 where swapIsCorrect i j = swap i j (swap j i s) `arrEq` s
          where arrEq a b = bAnd [readArray a k .== readArray b k | k <- [0 .. 255]]
                s = mkSFunArray id
