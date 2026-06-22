-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.BitPrecise.Adders
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Build two textbook binary adders out of logic gates and prove them correct,
-- fully automatically, by bit-blasting.
--
-- We model each adder as a Haskell function over a statically-known list of
-- symbolic bits, producing a fixed Boolean circuit. We then prove---for a
-- chosen word size---that the circuit computes the same result as SBV's native
-- bit-vector addition @(+)@:
--
--   * A /ripple-carry/ adder, which threads a carry sequentially through a
--     chain of full adders.
--
--   * A /carry-lookahead/ adder, which computes every carry directly from the
--     generate\/propagate signals of all lower bits, with no sequential
--     dependency.
--
-- Besides proving each adder equal to @(+)@, we also prove the two adders equal
-- to /each other/: the fast, parallel carry-lookahead circuit computes exactly
-- the same result as the simple ripple-carry reference.
--
-- All proofs here are discharged by a single decidable bit-vector query at a
-- fixed width. See "Documentation.SBV.Examples.TP.Adder" for the companion
-- development that instead proves a ripple-carry adder correct for /all/ widths
-- at once, by induction.
-----------------------------------------------------------------------------

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.BitPrecise.Adders where

import Data.SBV hiding (fullAdder)
import GHC.TypeLits (KnownNat)

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> :set -XDataKinds -XTypeApplications -XScopedTypeVariables
#endif

-- | A symbolic bit is just a symbolic boolean.
type Bit = SBool

-- * Logic gates

-- | A half adder takes two bits and produces their sum bit and carry bit:
-- @sum = a xor b@, @carry = a and b@.
halfAdder :: Bit -> Bit -> (Bit, Bit)
halfAdder a b = (a .<+> b, a .&& b)

-- | A full adder takes two bits and an incoming carry, and produces the sum bit
-- together with the outgoing carry. We build it out of two half adders, in the
-- usual way.
fullAdder :: Bit -> Bit -> Bit -> (Bit, Bit)
fullAdder a b cin = (s, c0 .|| c1)
  where (s0, c0) = halfAdder a b
        (s,  c1) = halfAdder s0 cin

-- * Ripple-carry adder

-- | The ripple-carry adder. Given an incoming carry and a little-endian list of
-- bit pairs (one pair per bit position, least-significant first), it threads the
-- carry through a chain of full adders, returning the list of sum bits together
-- with the final carry-out.
rippleAdd :: Bit -> [(Bit, Bit)] -> ([Bit], Bit)
rippleAdd cin []            = ([], cin)
rippleAdd cin ((a, b) : ps) = (s : ss, cout)
  where (s,  c)    = fullAdder a b cin
        (ss, cout) = rippleAdd c ps

-- * Carry-lookahead adder

-- | Generate and propagate signals for a bit position: a position /generates/ a
-- carry when both inputs are set, and /propagates/ an incoming carry when
-- exactly one input is set.
generatePropagate :: Bit -> Bit -> (Bit, Bit)
generatePropagate a b = (a .&& b, a .<+> b)

-- | The carry-lookahead adder. Rather than rippling the carry through the chain,
-- it computes the carry /into/ each position directly from the
-- generate\/propagate signals of all lower positions, using the textbook
-- expansion
--
-- @
--   c(i) = g(i-1) + p(i-1).g(i-2) + ... + p(i-1)...p(1).g(0) + p(i-1)...p(0).cin
-- @
--
-- so that every carry is an independent flat formula with no sequential
-- dependency. The sum bit at position @i@ is then @p(i) xor c(i)@, and the
-- carry-out is the carry into the (nonexistent) position just past the top.
lookaheadAdd :: Bit -> [(Bit, Bit)] -> ([Bit], Bit)
lookaheadAdd cin ps = (sums, carryInto n)
  where n   = length ps
        gps = [ generatePropagate a b | (a, b) <- ps ]

        g k = fst (gps !! k)
        p k = snd (gps !! k)

        -- product of the propagate signals over positions [lo .. hi-1]
        prodP lo hi = sAnd [ p k | k <- [lo .. hi - 1] ]

        -- carry into position i, expanded over all lower positions
        carryInto i = sOr $ (cin .&& prodP 0 i)
                          : [ g j .&& prodP (j + 1) i | j <- [0 .. i - 1] ]

        sums = [ p i .<+> carryInto i | i <- [0 .. n - 1] ]

-- * Lifting to words

-- | Run an adder over the bits of two words. We blast both operands into
-- little-endian bit lists, feed them to the adder with no incoming carry, and
-- reassemble the sum bits into a word. The carry-out is dropped, matching the
-- wrap-around semantics of bit-vector @(+)@.
addWith :: forall n. (KnownNat n, BVIsNonZero n) => (Bit -> [(Bit, Bit)] -> ([Bit], Bit)) -> SWord n -> SWord n -> SWord n
addWith adder x y = fromBitsLE ss
  where (ss, _) = adder sFalse (zip (blastLE x) (blastLE y))

-- | The ripple-carry adder, lifted to words.
rippleAddWord :: (KnownNat n, BVIsNonZero n) => SWord n -> SWord n -> SWord n
rippleAddWord = addWith rippleAdd

-- | The carry-lookahead adder, lifted to words.
lookaheadAddWord :: (KnownNat n, BVIsNonZero n) => SWord n -> SWord n -> SWord n
lookaheadAddWord = addWith lookaheadAdd

-- * Correctness

-- | The ripple-carry adder computes bit-vector addition. We prove it here at
-- width 8, but the same call proves it at any width you instantiate:
--
-- >>> rippleCorrect @8
-- Q.E.D.
--
-- Adder-versus-@(+)@ equivalence is one of the easy cases for bit-blasting (the
-- carry chain is linear), so this stays fast even at large widths---it is the
-- cheap baseline to compare the lookahead proofs against.
rippleCorrect :: forall n. (KnownNat n, BVIsNonZero n) => IO ThmResult
rippleCorrect = prove $ \(x :: SWord n) (y :: SWord n) -> rippleAddWord x y .== x + y

-- | The carry-lookahead adder computes bit-vector addition:
--
-- >>> lookaheadCorrect @8
-- Q.E.D.
--
-- Note that, unlike 'rippleCorrect', this proof slows down noticeably as the
-- width grows. The lookahead carry is the flat \(O(n^2)\) generate\/propagate
-- expansion, so the formula handed to the solver grows quadratically in the
-- width---try @lookaheadCorrect \@64@, @\@128@, @\@256@ to watch it climb.
lookaheadCorrect :: forall n. (KnownNat n, BVIsNonZero n) => IO ThmResult
lookaheadCorrect = prove $ \(x :: SWord n) (y :: SWord n) -> lookaheadAddWord x y .== x + y

-- | The fast carry-lookahead adder agrees with the simple ripple-carry adder on
-- every input---the parallel carry computation refines the sequential one:
--
-- >>> rippleEqLookahead @8
-- Q.E.D.
--
-- This proof drags in the same \(O(n^2)\) lookahead carry expansion as
-- 'lookaheadCorrect', so it scales the same way: comfortable at small widths,
-- visibly slower as the width grows.
rippleEqLookahead :: forall n. (KnownNat n, BVIsNonZero n) => IO ThmResult
rippleEqLookahead = prove $ \(x :: SWord n) (y :: SWord n) -> rippleAddWord x y .== lookaheadAddWord x y

-- | The carry-out of the ripple-carry adder is exactly the unsigned overflow
-- flag: it is set precisely when the true sum does not fit in @n@ bits, which
-- for an addition with no incoming carry is detectable as the result wrapping
-- below either operand:
--
-- >>> rippleOverflow @8
-- Q.E.D.
rippleOverflow :: forall n. (KnownNat n, BVIsNonZero n) => IO ThmResult
rippleOverflow = prove $ \(x :: SWord n) (y :: SWord n) ->
                   let (_, cout) = rippleAdd sFalse (zip (blastLE x) (blastLE y))
                   in cout .== ((x + y) .< x)
