-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.Multiply
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates how to use uninterpreted function models to synthesize
-- a simple two-bit multiplier.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Documentation.SBV.Examples.Uninterpreted.Multiply where

import Data.SBV

-- | The uninterpreted implementation of our 2x2 multiplier. We simply
-- receive two 2-bit values, and return the high and the low bit of the
-- resulting multiplication via two uninterpreted functions that we
-- called @mul22_hi@ and @mul22_lo@. Note that there is absolutely
-- no computation going on here, aside from simply passing the arguments
-- to the uninterpreted functions and stitching it back together.
--
-- NB. While definining @mul22_lo@ we used our domain knowledge that the
-- low-bit of the multiplication only depends on the low bits of the inputs.
-- However, this is merely a simplifying assumption; we could have passed
-- all the arguments as well.
mul22 :: (SBool, SBool) -> (SBool, SBool) -> (SBool, SBool)
mul22 (a1, a0) (b1, b0) = (mul22_hi, mul22_lo)
  where mul22_hi = uninterpret "mul22_hi" a1 a0 b1 b0
        mul22_lo = uninterpret "mul22_lo"    a0    b0


-- | Synthesize a 2x2 multiplier. We use 8-bit inputs merely because that is
-- the lowest bit-size SBV supports but that is more or less irrelevant. (Larger
-- sizes would work too.) We simply assert this for all input values, extract
-- the bottom two bits, and assert that our "uninterpreted" implementation in 'mul22'
-- is precisely the same. We have:
--
-- >>> sat synthMul22
-- Satisfiable. Model:
--   mul22_hi :: Bool -> Bool -> Bool -> Bool -> Bool
--   mul22_hi False True  True  False = True
--   mul22_hi False True  True  True  = True
--   mul22_hi True  False False True  = True
--   mul22_hi True  False True  True  = True
--   mul22_hi True  True  False True  = True
--   mul22_hi True  True  True  False = True
--   mul22_hi _     _     _     _     = False
-- <BLANKLINE>
--   mul22_lo :: Bool -> Bool -> Bool
--   mul22_lo True True = True
--   mul22_lo _    _    = False
--
-- It is easy to see that the low bit is simply the logical-and of the low bits. It takes a moment of
-- staring, but you can see that the high bit is correct as well: The logical formula is @a1b xor a0b1@,
-- and if you work out the truth-table presented, you'll see that it is exactly that. Of course,
-- you can use SBV to prove this. First, define the model we were given to make it symbolic:
--
-- >>> :{
-- mul22_hi :: SBool -> SBool -> SBool -> SBool -> SBool
-- mul22_hi a1 a0 b1 b0 = ite ([a1, a0, b1, b0] .== [sFalse, sTrue , sTrue , sFalse]) sTrue
--                      $ ite ([a1, a0, b1, b0] .== [sFalse, sTrue , sTrue , sTrue ]) sTrue
--                      $ ite ([a1, a0, b1, b0] .== [sTrue , sFalse, sFalse, sTrue ]) sTrue
--                      $ ite ([a1, a0, b1, b0] .== [sTrue , sFalse, sTrue , sTrue ]) sTrue
--                      $ ite ([a1, a0, b1, b0] .== [sTrue , sTrue , sFalse, sTrue ]) sTrue
--                      $ ite ([a1, a0, b1, b0] .== [sTrue , sTrue , sTrue , sFalse]) sTrue
--                        sFalse
-- :}
--
-- Now we can say:
--
-- >>> prove $ \a1 a0 b1 b0 -> mul22_hi a1 a0 b1 b0 .== (a1 .&& b0) .<+> (a0 .&& b1)
-- Q.E.D.
--
-- and rest assured that we have a correctly synthesized circuit!
synthMul22 :: Goal
synthMul22 = do a :: SWord8 <- forall "a"
                b :: SWord8 <- forall "b"

                let lsb2 x = let [x1, x0] = reverse $ take 2 $ blastLE x
                             in (x1, x0)

                constrain $ mul22 (lsb2 a) (lsb2 b) .== lsb2 (a * b)
