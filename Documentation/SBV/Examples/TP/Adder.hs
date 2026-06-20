-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Adder
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Prove a ripple-carry adder correct by induction, for /all/ widths at once.
--
-- This is the inductive companion to
-- "Documentation.SBV.Examples.BitPrecise.Adders", which proves a fixed-width
-- adder correct automatically by bit-blasting. Here, instead, we model the
-- operands as arbitrary-length, little-endian symbolic bit lists and prove---by
-- induction on the list---that the adder agrees with the mathematical value of
-- the bits, with no bound on the width.
--
-- A number is represented by a little-endian list of bit pairs: one
-- @(a, b)@ per position, least-significant first, where @a@ is a bit of the
-- first operand and @b@ the corresponding bit of the second. The integer value
-- of such a list is @sum_i bit_i * 2^i@.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Adder where

import Prelude hiding (fst, snd)

import Data.SBV hiding (fullAdder)
import Data.SBV.Tuple
import Data.SBV.TP

-- We reuse the very same combinational gates that the fixed-width, bit-blasted
-- companion proves correct---only the adder driver differs (a symbolic,
-- inductive recursion here versus a metalevel one there). The 'Data.SBV.fullAdder'
-- word-level operation is hidden above so 'fullAdder' refers to that gate.
import Documentation.SBV.Examples.BitPrecise.Adders (Bit, fullAdder)

#ifdef DOCTEST
-- $setup
-- >>> :set -XOverloadedLists
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Bits, values, and the adder

-- | The integer value of a single bit: @1@ if set, @0@ otherwise.
bitVal :: Bit -> SInteger
bitVal b = ite b 1 0

-- | The integer value of a little-endian bit list: @sum_i bit_i * 2^i@.
val :: SList Bool -> SInteger
val = smtFunction "val"
    $ \bs -> [sCase| bs of
                []     -> 0
                x : xs -> bitVal x + 2 * val xs
             |]

-- | The value of the first operand, read off the first components of the pairs.
valA :: SList (Bool, Bool) -> SInteger
valA = smtFunction "valA"
     $ \ps -> [sCase| ps of
                 []          -> 0
                 (a, _) : qs -> bitVal a + 2 * valA qs
              |]

-- | The value of the second operand, read off the second components of the pairs.
valB :: SList (Bool, Bool) -> SInteger
valB = smtFunction "valB"
     $ \ps -> [sCase| ps of
                 []          -> 0
                 (_, b) : qs -> bitVal b + 2 * valB qs
              |]

-- | The ripple-carry adder. Given an incoming carry and a little-endian list of
-- bit pairs, thread the carry through a chain of full adders (the same
-- 'fullAdder' gate the bit-blasted companion verifies), emitting each sum bit
-- and, at the end, the final carry-out as the most-significant bit. The result
-- is therefore one bit longer than the input, so its value is exactly the full
-- sum---no truncation.
rca :: Bit -> SList (Bool, Bool) -> SList Bool
rca = smtFunction "rca"
    $ \c ps -> [sCase| ps of
                  []     -> [c]
                  p : qs -> let (s, co) = fullAdder (fst p) (snd p) c
                            in s .: rca co qs
               |]

-- * Correctness

-- | The ripple-carry adder computes the sum of its operands, for any width:
--
-- @val (rca 0 ps) == valA ps + valB ps@
--
-- We prove it via a more general lemma that tracks the incoming carry, since the
-- recursive calls feed each stage's carry-out into the next.
--
-- >>> runTP correctness
-- Lemma: fullAdderCorrect        Q.E.D.
-- Inductive lemma: rcaCorrect
--   Step: Base                   Q.E.D.
--   Step: 1                      Q.E.D.
--   Step: 2                      Q.E.D.
--   Step: 3                      Q.E.D.
--   Step: 4                      Q.E.D.
--   Step: 5                      Q.E.D.
--   Result:                      Q.E.D.
-- Lemma: adderCorrect            Q.E.D.
-- Functions proven terminating: rca, val, valA, valB
-- [Proven] adderCorrect :: Ɐps ∷ [(Bool, Bool)] → Bool
correctness :: TP (Proof (Forall "ps" [(Bool, Bool)] -> SBool))
correctness = do

  -- A single full adder is arithmetically correct: the sum bit plus twice the
  -- carry-out equals the sum of the three input bits. This is a finite boolean
  -- fact, discharged directly.
  faC <- lemma "fullAdderCorrect"
               (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) ->
                    let (s, co) = fullAdder a b c
                    in bitVal s + 2 * bitVal co .== bitVal a + bitVal b + bitVal c)
               []

  -- The general statement, tracking the incoming carry. Induct on the list of
  -- bit pairs; the carry is universally quantified so the induction hypothesis
  -- applies at the carry-out fed to the recursive call.
  rcaC <- induct "rcaCorrect"
                 (\(Forall @"ps" ps) (Forall @"c" c) ->
                      val (rca c ps) .== valA ps + valB ps + bitVal c) $
                 \ih (p, ps) c ->
                     let a       = fst p
                         b       = snd p
                         (s, co) = fullAdder a b c
                     in [] |- val (rca c (p .: ps))
                           =: val (s .: rca co ps)
                           =: bitVal s + 2 * val (rca co ps)
                           ?? ih `at` Inst @"c" co
                           =: bitVal s + 2 * (valA ps + valB ps + bitVal co)
                           ?? faC `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c)
                           =: (bitVal a + 2 * valA ps) + (bitVal b + 2 * valB ps) + bitVal c
                           =: valA (p .: ps) + valB (p .: ps) + bitVal c
                           =: qed

  -- The headline corollary: with no incoming carry, the adder computes the sum.
  lemma "adderCorrect"
        (\(Forall ps) -> val (rca sFalse ps) .== valA ps + valB ps)
        [proofOf rcaC]
