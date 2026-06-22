-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Adder
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Prove binary adders correct by induction, for /all/ widths at once.
--
-- This is the inductive companion to
-- "Documentation.SBV.Examples.BitPrecise.Adders", which proves fixed-width
-- adders correct automatically by bit-blasting. Here, instead, we model the
-- operands as arbitrary-length, little-endian symbolic bit lists and prove---by
-- induction on the list---properties that hold with no bound on the width:
--
--   * a ripple-carry adder agrees with the mathematical value of the bits
--     (@correctness@);
--
--   * a parallel-prefix (carry-lookahead) tree computes the same carry as the
--     ripple, because the generate\/propagate carry operator is associative
--     (@lookaheadCorrect@); and
--
--   * that lookahead carry is exactly the carry the ripple adder threads
--     (@lookaheadMatchesAdder@).
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

import Prelude hiding (fst, snd, foldl, map, curry, uncurry, (++))

import Data.SBV hiding (fullAdder)
import Data.SBV.List (foldl, map, (++))
import Data.SBV.Tuple
import Data.SBV.TP

import Documentation.SBV.Examples.TP.Lists (foldlOverAppend)

-- We reuse the very same combinational gates that the fixed-width, bit-blasted
-- companion proves correct---only the adder driver differs (a symbolic,
-- inductive recursion here versus a metalevel one there). The 'Data.SBV.fullAdder'
-- word-level operation is hidden above so 'fullAdder' refers to that gate.
import Documentation.SBV.Examples.BitPrecise.Adders (Bit, fullAdder, generatePropagate)

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
                  p : qs -> let (s, co) = uncurry fullAdder p c
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

-- * Carry-lookahead, via a parallel-prefix tree
--
-- $lookahead
-- A ripple-carry adder is slow because each stage waits for the carry from the
-- one below it. A /carry-lookahead/ adder breaks that chain by computing the
-- carries in parallel. The key is to summarize a contiguous block of positions
-- by a @(generate, propagate)@ /section/: whether the block produces a carry on
-- its own (@generate@), and whether it would pass an incoming carry straight
-- through (@propagate@). Adjacent sections combine with the associative operator
-- 'dot', so the carries can be gathered by a balanced /tree/ of 'dot's rather
-- than a linear ripple.
--
-- We prove that tree correct against the ripple as follows. 'dot' is an
-- associative monoid with identity 'idSec', and applying a section to an
-- incoming carry ('applyC') is its action. The ripple carry is the /linear/
-- fold of 'dot' over the sections ('carryIsFold'), and a balanced tree of 'dot's
-- computes that /same/ fold by associativity ('treeIsFold'). Hence the parallel
-- tree and the sequential ripple agree.

-- | Combine two adjacent @(generate, propagate)@ sections, lower-order first.
-- The combined block generates a carry if the high part does, or if it
-- propagates one generated by the low part; it propagates only if both do.
dot :: SBV (Bool, Bool) -> SBV (Bool, Bool) -> SBV (Bool, Bool)
dot lo hi = tuple (fst hi .|| (snd hi .&& fst lo), snd hi .&& snd lo)

-- | The identity section: generates nothing, propagates everything.
idSec :: SBV (Bool, Bool)
idSec = tuple (sFalse, sTrue)

-- | Apply a section to an incoming carry, giving the carry out of that section.
applyC :: SBV (Bool, Bool) -> Bit -> Bit
applyC sec c = fst sec .|| (snd sec .&& c)

-- | The sequential ripple carry-out: thread the incoming carry through the
-- sections, left to right.
carry :: Bit -> SList (Bool, Bool) -> Bit
carry = smtFunction "carry"
      $ \c gps -> [sCase| gps of
                     []       -> c
                     b : rest -> carry (applyC b c) rest
                  |]

-- | The @(generate, propagate)@ section of a single operand bit-pair @(a, b)@,
-- using the very same 'generatePropagate' gate as the bit-blasted companion.
gpOf :: SBV (Bool, Bool) -> SBV (Bool, Bool)
gpOf p = tuple (uncurry generatePropagate p)

-- | The carry-out actually threaded by the ripple adder 'rca': fold the
-- incoming carry through the full-adder carry of each position. (This is 'rca'
-- with the sum bits dropped---it threads the identical carry, via the same
-- 'fullAdder'.)
rcaCarry :: Bit -> SList (Bool, Bool) -> Bit
rcaCarry = smtFunction "rcaCarry"
         $ \c ps -> [sCase| ps of
                       []     -> c
                       p : qs -> let (_, co) = uncurry fullAdder p c
                                 in rcaCarry co qs
                    |]

-- | The headline lookahead result, in textbook parallel-prefix form: the ripple
-- carry over a concatenation equals combining the two halves' sections
-- /independently/ and then applying the result to the incoming carry. Since
-- 'dot' is associative, the halves can be split the same way recursively---so
-- the carries can be gathered by a balanced /tree/ of 'dot's instead of a linear
-- ripple, and this says every such tree computes the same carry.
--
-- The proof rests on two pieces: 'carryIsFold' (the ripple carry /is/ the linear
-- fold of 'dot'), kept as its own reusable lemma, and 'foldlDotSplit' (the fold
-- distributes over append---the associativity law that licenses any tree).
--
-- >>> runTP lookaheadCorrect
-- Lemma: dotAssoc                     Q.E.D.
-- Lemma: dotLeftUnit                  Q.E.D.
-- Lemma: applyCDot                    Q.E.D.
-- Inductive lemma: foldlDotShift
--   Step: Base                        Q.E.D.
--   Step: 1                           Q.E.D.
--   Step: 2                           Q.E.D.
--   Step: 3                           Q.E.D.
--   Step: 4                           Q.E.D.
--   Step: 5                           Q.E.D.
--   Step: 6                           Q.E.D.
--   Result:                           Q.E.D.
-- Inductive lemma: carryIsFold
--   Step: Base                        Q.E.D.
--   Step: 1                           Q.E.D.
--   Step: 2                           Q.E.D.
--   Step: 3                           Q.E.D.
--   Step: 4                           Q.E.D.
--   Step: 5                           Q.E.D.
--   Step: 6                           Q.E.D.
--   Result:                           Q.E.D.
-- Inductive lemma: foldlOverAppend
--   Step: Base                        Q.E.D.
--   Step: 1                           Q.E.D.
--   Step: 2                           Q.E.D.
--   Step: 3                           Q.E.D.
--   Result:                           Q.E.D.
-- Lemma: foldlDotSplit
--   Step: 1                           Q.E.D.
--   Step: 2                           Q.E.D.
--   Result:                           Q.E.D.
-- Lemma: treeCarry
--   Step: 1                           Q.E.D.
--   Step: 2                           Q.E.D.
--   Result:                           Q.E.D.
-- Functions proven terminating: carry, sbv.foldl
-- [Proven] treeCarry :: Ɐc ∷ Bool → Ɐxs ∷ [(Bool, Bool)] → Ɐys ∷ [(Bool, Bool)] → Bool
lookaheadCorrect :: TP (Proof (Forall "c" Bool -> Forall "xs" [(Bool, Bool)] -> Forall "ys" [(Bool, Bool)] -> SBool))
lookaheadCorrect = do

  -- 'dot' is an associative monoid with identity 'idSec'; 'applyC' is its
  -- action. All finite boolean facts.
  assoc <- lemma "dotAssoc"    (\(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> dot x (dot y z) .== dot (dot x y) z)                  []
  lunit <- lemma "dotLeftUnit" (\(Forall @"x" x) -> dot idSec x .== x)                                                                    []
  act   <- lemma "applyCDot"   (\(Forall @"lo" lo) (Forall @"hi" hi) (Forall @"c" c) -> applyC (dot lo hi) c .== applyC hi (applyC lo c)) []

  -- Folding with an initial section @s@ equals @s@ combined with the fold from
  -- the identity. (Accumulator reassociation, à la Lists.foldrFoldl.)
  fldShift <- induct "foldlDotShift"
                  (\(Forall @"xs" xs) (Forall @"s" s) ->
                       foldl dot s xs .== dot s (foldl dot idSec xs)) $
                  \ih (x, xs) s -> [] |- foldl dot s (x .: xs)
                                      =: foldl dot (dot s x) xs
                                      ?? ih `at` Inst @"s" (dot s x)
                                      =: dot (dot s x) (foldl dot idSec xs)
                                      ?? assoc
                                      =: dot s (dot x (foldl dot idSec xs))
                                      ?? ih `at` Inst @"s" x
                                      =: dot s (foldl dot x xs)
                                      ?? lunit
                                      =: dot s (foldl dot (dot idSec x) xs)
                                      =: dot s (foldl dot idSec (x .: xs))
                                      =: qed

  -- The reusable link: the sequential ripple carry is the left fold of 'dot'
  -- over the sections, applied to the incoming carry. Induct on the sections;
  -- the carry is the threaded argument, so the hypothesis applies at the next
  -- carry-in.
  cif <- induct "carryIsFold"
                (\(Forall @"gps" gps) (Forall @"c" c) ->
                     carry c gps .== applyC (foldl dot idSec gps) c) $
                \ih (b, gps) c -> [] |- carry c (b .: gps)
                                     =: carry (applyC b c) gps
                                     ?? ih `at` Inst @"c" (applyC b c)
                                     =: applyC (foldl dot idSec gps) (applyC b c)
                                     ?? act `at` (Inst @"lo" b, Inst @"hi" (foldl dot idSec gps), Inst @"c" c)
                                     =: applyC (dot b (foldl dot idSec gps)) c
                                     ?? fldShift `at` (Inst @"xs" gps, Inst @"s" b)
                                     =: applyC (foldl dot b gps) c
                                     ?? lunit
                                     =: applyC (foldl dot (dot idSec b) gps) c
                                     =: applyC (foldl dot idSec (b .: gps)) c
                                     =: qed

  -- foldl of 'dot' distributes over append (imported from the Lists examples).
  foa <- foldlOverAppend dot

  -- The split/homomorphism law: reducing a concatenation equals reducing the
  -- halves independently and combining them with 'dot'. This is what licenses
  -- any balanced (tree) grouping of the sections.
  splitLaw <- calc "foldlDotSplit"
                (\(Forall @"xs" xs) (Forall @"ys" ys) ->
                     foldl dot idSec (xs ++ ys) .== dot (foldl dot idSec xs) (foldl dot idSec ys)) $
                \xs ys -> [] |- foldl dot idSec (xs ++ ys)
                             ?? foa `at` (Inst @"xs" xs, Inst @"ys" ys, Inst @"e" idSec)
                             =: foldl dot (foldl dot idSec xs) ys
                             ?? fldShift `at` (Inst @"xs" ys, Inst @"s" (foldl dot idSec xs))
                             =: dot (foldl dot idSec xs) (foldl dot idSec ys)
                             =: qed

  -- Headline: the ripple carry of a concatenation equals applying the
  -- independently-combined half-sections to the incoming carry.
  calc "treeCarry"
       (\(Forall @"c" c) (Forall @"xs" xs) (Forall @"ys" ys) ->
            carry c (xs ++ ys) .== applyC (dot (foldl dot idSec xs) (foldl dot idSec ys)) c) $
       \c xs ys -> [] |- carry c (xs ++ ys)
                    ?? cif `at` (Inst @"gps" (xs ++ ys), Inst @"c" c)
                    =: applyC (foldl dot idSec (xs ++ ys)) c
                    ?? splitLaw `at` (Inst @"xs" xs, Inst @"ys" ys)
                    =: applyC (dot (foldl dot idSec xs) (foldl dot idSec ys)) c
                    =: qed

-- | The capstone, tying the lookahead machinery back to the actual adder:
-- running the (foldable, tree-groupable) section 'carry' over the operands'
-- generate\/propagate signals reproduces exactly the carry that the ripple adder
-- 'rca' threads. Combined with 'treeCarry', this says the adder's own carry can
-- be computed by any balanced prefix tree.
--
-- >>> runTP lookaheadMatchesAdder
-- Lemma: applyCgpOf                         Q.E.D.
-- Inductive lemma: lookaheadMatchesAdder
--   Step: Base                              Q.E.D.
--   Step: 1                                 Q.E.D.
--   Step: 2                                 Q.E.D.
--   Step: 3                                 Q.E.D.
--   Step: 4                                 Q.E.D.
--   Step: 5                                 Q.E.D.
--   Result:                                 Q.E.D.
-- Functions proven terminating: carry, rcaCarry, sbv.map
-- [Proven] lookaheadMatchesAdder :: Ɐps ∷ [(Bool, Bool)] → Ɐc ∷ Bool → Bool
lookaheadMatchesAdder :: TP (Proof (Forall "ps" [(Bool, Bool)] -> Forall "c" Bool -> SBool))
lookaheadMatchesAdder = do

  -- Applying a position's generate/propagate section to a carry is exactly the
  -- full-adder carry-out. A finite boolean fact.
  applyGP <- lemma "applyCgpOf"
                   (\(Forall @"p" p) (Forall @"c" c) ->
                        let (_, co) = uncurry fullAdder p c
                        in applyC (gpOf p) c .== co)
                   []

  -- Induct on the operands; the carry is threaded, so the hypothesis applies at
  -- the next carry-in.
  induct "lookaheadMatchesAdder"
         (\(Forall @"ps" ps) (Forall @"c" c) -> carry c (map gpOf ps) .== rcaCarry c ps) $
         \ih (p, ps) c -> let (_, co) = uncurry fullAdder p c
                          in [] |- carry c (map gpOf (p .: ps))
                                =: carry c (gpOf p .: map gpOf ps)
                                =: carry (applyC (gpOf p) c) (map gpOf ps)
                                ?? applyGP `at` (Inst @"p" p, Inst @"c" c)
                                =: carry co (map gpOf ps)
                                ?? ih `at` Inst @"c" co
                                =: rcaCarry co ps
                                =: rcaCarry c (p .: ps)
                                =: qed
