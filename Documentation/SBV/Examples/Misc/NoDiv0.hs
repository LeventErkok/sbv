-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.NoDiv0
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates SBV's assertion checking facilities
-----------------------------------------------------------------------------

{-# LANGUAGE ImplicitParams #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.NoDiv0 where

import Data.SBV
import GHC.Stack

-- | A simple variant of division, where we explicitly require the
-- caller to make sure the divisor is not 0.
checkedDiv :: (?loc :: CallStack) => SInt32 -> SInt32 -> SInt32
checkedDiv x y = sAssert (Just ?loc)
                         "Divisor should not be 0"
                         (y ./= 0)
                         (x `sDiv` y)

-- | Check whether an arbitrary call to 'checkedDiv' is safe. Clearly, we do not expect
-- this to be safe:
--
-- >>> test1
-- [./Documentation/SBV/Examples/Misc/NoDiv0.hs:38:14:checkedDiv: Divisor should not be 0: Violated. Model:
--   s0 = 0 :: Int32
--   s1 = 0 :: Int32]
--
test1 :: IO [SafeResult]
test1 = safe checkedDiv

-- | Repeat the test, except this time we explicitly protect against the bad case. We have:
--
-- >>> test2
-- [./Documentation/SBV/Examples/Misc/NoDiv0.hs:46:41:checkedDiv: Divisor should not be 0: No violations detected]
--
test2 :: IO [SafeResult]
test2 = safe $ \x y -> ite (y .== 0) 3 (checkedDiv x y)
