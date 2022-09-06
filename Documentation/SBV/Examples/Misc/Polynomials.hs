-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Polynomials
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Simple usage of polynomials over GF(2^n), using Rijndael's
-- finite field: <http://en.wikipedia.org/wiki/Finite_field_arithmetic#Rijndael.27s_finite_field>
--
-- The functions available are:
--
--  [/pMult/] GF(2^n) Multiplication
--
--  [/pDiv/] GF(2^n) Division
--
--  [/pMod/] GF(2^n) Modulus
--
--  [/pDivMod/] GF(2^n) Division/Modulus, packed together
--
-- Note that addition in GF(2^n) is simply `xor`, so no custom function is provided.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Polynomials where

import Data.SBV
import Data.SBV.Tools.Polynomial

-- | Helper synonym for representing GF(2^8); which are merely 8-bit unsigned words. Largest
-- term in such a polynomial has degree 7.
type GF28 = SWord8

-- | Multiplication in Rijndael's field; usual polynomial multiplication followed by reduction
-- by the irreducible polynomial.  The irreducible used by Rijndael's field is the polynomial
-- @x^8 + x^4 + x^3 + x + 1@, which we write by giving it's /exponents/ in SBV.
-- See: <http://en.wikipedia.org/wiki/Finite_field_arithmetic#Rijndael.27s_finite_field>.
-- Note that the irreducible itself is not in GF28! It has a degree of 8.
--
-- NB. You can use the 'showPoly' function to print polynomials nicely, as a mathematician would write.
gfMult :: GF28 -> GF28 -> GF28
a `gfMult` b = pMult (a, b, [8, 4, 3, 1, 0])

-- | States that the unit polynomial @1@, is the unit element
multUnit :: GF28 -> SBool
multUnit x = (x `gfMult` unit) .== x
  where unit = polynomial [0]   -- x@0

-- | States that multiplication is commutative
multComm :: GF28 -> GF28 -> SBool
multComm x y = (x `gfMult` y) .== (y `gfMult` x)

-- | States that multiplication is associative, note that associativity
-- proofs are notoriously hard for SAT/SMT solvers
multAssoc :: GF28 -> GF28 -> GF28 -> SBool
multAssoc x y z = ((x `gfMult` y) `gfMult` z) .== (x `gfMult` (y `gfMult` z))

-- | States that the usual multiplication rule holds over GF(2^n) polynomials
-- Checks:
--
-- @
--    if (a, b) = x `pDivMod` y then x = y `pMult` a + b
-- @
--
-- being careful about @y = 0@. When divisor is 0, then quotient is
-- defined to be 0 and the remainder is the numerator.
-- (Note that addition is simply `xor` in GF(2^8).)
polyDivMod :: GF28 -> GF28 -> SBool
polyDivMod x y = ite (y .== 0) ((0, x) .== (a, b)) (x .== (y `gfMult` a) `xor` b)
  where (a, b) = x `pDivMod` y

-- | Queries
testGF28 :: IO ()
testGF28 = do
  print =<< prove multUnit
  print =<< prove multComm
  -- print =<< prove multAssoc -- takes too long; see above note..
  print =<< prove polyDivMod
