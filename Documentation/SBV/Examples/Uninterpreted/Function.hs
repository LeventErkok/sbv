-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.Function
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates function counter-examples
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Uninterpreted.Function where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | An uninterpreted function
f :: SWord8 -> SWord8 -> SWord16
f = uninterpret "f"

-- | Asserts that @f x z == f (y+2) z@ whenever @x == y+2@. Naturally correct:
--
-- >>> prove thmGood
-- Q.E.D.
thmGood :: SWord8 -> SWord8 -> SWord8 -> SBool
thmGood x y z = x .== y+2 .=> f x z .== f (y + 2) z
