-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.AUF
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Formalizes and proves the following theorem about arithmetic,
-- uninterpreted functions, and arrays. (For reference, see <http://research.microsoft.com/en-us/um/redmond/projects/z3/fmcad06-slides.pdf>
-- slide number 24):
--
-- @
--    x + 2 = y  implies  f (read (write (a, x, 3), y - 2)) = f (y - x + 1)
-- @
--
-- We interpret the types as follows (other interpretations certainly possible):
--
--    [/x/] 'SWord32' (32-bit unsigned address)
--
--    [/y/] 'SWord32' (32-bit unsigned address)
--
--    [/a/] An array, indexed by 32-bit addresses, returning 32-bit unsigned integers
--
--    [/f/] An uninterpreted function of type @'SWord32' -> 'SWord64'@
--
-- The function @read@ and @write@ are usual array operations.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Uninterpreted.AUF where

import Data.SBV

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
#endif

-- | Uninterpreted function in the theorem
f :: SWord32 -> SWord64
f = uninterpret "f"

-- | Correctness theorem. We state it for all values of @x@, @y@, and the given array @a@. We have:
--
-- >>> prove thm
-- Q.E.D.
thm :: SWord32 -> SWord32 -> SArray Word32 Word32 -> SBool
thm x y a = lhs .=> rhs
  where lhs = x + 2 .== y
        rhs =     f (readArray (writeArray a x 3) (y - 2))
              .== f (y - x + 1)
