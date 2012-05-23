-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Uninterpreted.AUF
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Formalizes and proves the following theorem, about arithmetic,
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

module Data.SBV.Examples.Uninterpreted.AUF where

import Data.SBV

--------------------------------------------------------------
-- * Model using functional arrays
--------------------------------------------------------------

-- | The array type, takes symbolic 32-bit unsigned indexes
-- and stores 32-bit unsigned symbolic values. These are
-- functional arrays where reading before writing a cell
-- throws an exception.
type A = SFunArray Word32 Word32

-- | Uninterpreted function in the theorem
f :: SWord32 -> SWord64
f = uninterpret "f"

-- | Correctness theorem. We state it for all values of @x@, @y@, and 
-- the array @a@. We also take an arbitrary initializer for the array.
thm1 :: SWord32 -> SWord32 -> A -> SWord32 -> SBool
thm1 x y a initVal = lhs ==> rhs
  where a'  = resetArray a initVal -- initialize array
        lhs = x + 2 .== y
        rhs =     f (readArray (writeArray a' x 3) (y - 2))
              .== f (y - x + 1)

-- | Prints Q.E.D. when run, as expected
--
-- >>> proveThm1
-- Q.E.D.
proveThm1 :: IO ()
proveThm1 = print =<< prove thm1

--------------------------------------------------------------
-- * Model using SMT arrays
--------------------------------------------------------------

-- | This version directly uses SMT-arrays and hence does not need an initializer.
-- Reading an element before writing to it returns an arbitrary value.
type B = SArray Word32 Word32

-- | Same as 'thm1', except we don't need an initializer with the 'SArray' model.
thm2 :: SWord32 -> SWord32 -> B -> SBool
thm2 x y a = lhs ==> rhs
  where lhs = x + 2 .== y
        rhs =     f (readArray (writeArray a x 3) (y - 2))
              .== f (y - x + 1)

-- | Prints Q.E.D. when run, as expected:
--
-- >>> proveThm2
-- Q.E.D.
proveThm2 :: IO ()
proveThm2 = print =<< prove thm2
