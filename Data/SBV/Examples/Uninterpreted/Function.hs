-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Uninterpreted.Function
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates function counter-examples
-----------------------------------------------------------------------------

module Data.SBV.Examples.Uninterpreted.Function where

import Data.SBV
import qualified Data.SBV.Provers.Yices as Yices

-- | An uninterpreted function
f :: SWord8 -> SWord8 -> SWord16
f = uninterpret "f"

-- | Asserts that @f x z == f (y+2) z@ whenever @x == y+2@. Naturally correct:
--
-- >>> prove thmGood
-- Q.E.D.
thmGood :: SWord8 -> SWord8 -> SWord8 -> SBool
thmGood x y z = x .== y+2 ==> f x z .== f (y + 2) z

-- | Asserts that @f@ is commutative; which is not necessarily true!
-- Indeed, the SMT solver returns a counter-example function that is
-- not commutative. (Note that we have to use Yices as Z3 function
-- counterexamples are not yet supported by sbv.) We have:
--
--
-- >>> proveWith yicesSMT09 $ forAll ["x", "y"] thmBad
-- Falsifiable. Counter-example:
--   x = 0 :: Word8
--   y = 128 :: Word8
--   -- uninterpreted: f
--        f 128 0 = 32768
--        f _   _ = 0
--
-- Note how the counterexample function @f@ returned by Yices violates commutativity;
-- thus providing evidence that the asserted theorem is not valid.
thmBad :: SWord8 -> SWord8 -> SBool
thmBad x y = f x y .== f y x

-- | Old version of Yices, which supports nice output for uninterpreted functions.
yicesSMT09 :: SMTConfig
yicesSMT09 = yices {solver = yices'}
  where yices' = Yices.yices { options    = ["-m"]
                             , executable = "yices-SMT09"
                             }

----------------------------------------------------------------------
-- * Inspecting symbolic traces
----------------------------------------------------------------------

-- | A symbolic trace can help illustrate the action of Ladner-Fischer. This
