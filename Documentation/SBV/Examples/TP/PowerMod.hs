-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.PowerMod
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proofs about power and modulus. Adapted from an example by amigalemming,
-- see <http://github.com/LeventErkok/sbv/issues/744>.
--
-- We also demonstrate the proof-caching features of TP.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.PowerMod where

import Data.SBV
import Data.SBV.Tools.TP

-- | The proofs in this module are structured so they are presented at the top-level and reused.
-- This results in re-running the proofs over and over, as each proof has to run all its dependents.
-- To avoid re-running proofs, we tell TP to use a proof-cache. Note that use of a proof-cache comes
-- with the user obligation that all proofs used are uniquely named. Otherwise the results can be
-- unsound, and SBV will indicate this possibility in its output.
runCached :: TP a -> IO a
runCached = runTPWith (tpCache z3)

-- | Power function over integers.
power :: SInteger -> SInteger -> SInteger
power = smtFunction "power" $ \b n -> ite (n .<= 0) 1 (b * power b (n-1))

-- | \(m > 1 \Rightarrow n + mk \equiv n \pmod{m}\)
--
-- >>> runCached modAddMultiple
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modAddMultiple
modAddMultiple :: TP Proof
modAddMultiple = do
   inductWith (tpCache cvc5) "modAddMultiple"
      (\(Forall @"k" k) (Forall @"n" n) (Forall @"m" m) -> m .> 1 .=> (n + m*k) `sEMod` m .== n `sEMod` m) $
      \ih k n m -> [m .> 1] |- (n + m*(k+1)) `sEMod` m
                            =: (n + m*k + m) `sEMod` m
                            =: (n + m*k) `sEMod` m
                            ?? ih `at` (Inst @"n" n, Inst @"m" m)
                            =: n `sEMod` m
                            =: qed

-- | \(m > 0 \Rightarrow a + b \equiv a + (b \bmod m) \pmod{m}\)
--
-- >>> runCached modAddRight
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modAddRight
modAddRight :: TP Proof
modAddRight = do
   mAddMul <- modAddMultiple
   calc "modAddRight"
      (\(Forall @"a" a) (Forall @"b" b) (Forall @"m" m) -> m .> 0  .=>  (a+b) `sEMod` m .== (a + b `sEMod` m) `sEMod` m) $
      \a b m -> [m .> 0] |- (a+b) `sEMod` m
                         =: (a + b `sEMod` m + m * b `sEDiv` m) `sEMod` m
                         ?? mAddMul `at` (Inst @"k" (b `sEDiv` m), Inst @"n" (a + b `sEMod` m), Inst @"m" m)
                         =: (a + b `sEMod` m) `sEMod` m
                         =: qed

-- | \(m > 0 \Rightarrow a + b \equiv (a \bmod m) + b \pmod{m}\)
--
-- >>> runCached modAddLeft
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modAddLeft
modAddLeft :: TP Proof
modAddLeft = do
   mAddR <- modAddRight
   calc "modAddLeft"
      (\(Forall @"a" a) (Forall @"b" b) (Forall @"m" m) -> m .> 0 .=>  (a+b) `sEMod` m .== (a `sEMod` m + b) `sEMod` m) $
      \a b m -> [m .> 0] |- (a+b) `sEMod` m
                         =: (b+a) `sEMod` m
                         ?? mAddR
                         =: (b + a `sEMod` m) `sEMod` m
                         =: (a `sEMod` m + b) `sEMod` m
                         =: qed

-- | \(m > 0 \Rightarrow a - b \equiv a - (b \bmod m) \pmod{m}\)
--
-- >>> runCached modSubRight
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modSubRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modSubRight
modSubRight :: TP Proof
modSubRight = do
   mAddMul <- modAddMultiple
   calc "modSubRight"
      (\(Forall @"a" a) (Forall @"b" b) (Forall @"m" m) -> m .> 0 .=>  (a-b) `sEMod` m .== (a - b `sEMod` m) `sEMod` m) $
      \a b m -> [m .> 0] |- (a-b) `sEMod` m
                         =: (a - (b `sEMod` m + m * b `sEDiv` m)) `sEMod` m
                         =: ((a - b `sEMod` m) + m*(- (b `sEDiv` m))) `sEMod` m
                         ?? mAddMul `at` (Inst @"k" (- (b `sEDiv` m)), Inst @"n" (a - b `sEMod` m), Inst @"m" m)
                         =: (a - b `sEMod` m) `sEMod` m
                         =: qed

-- | \(a \geq 0 \land m > 0 \Rightarrow ab \equiv a \cdot (b \bmod m) \pmod{m}\)
--
-- >>> runCached modMulRightNonneg
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Inductive lemma: modMulRightNonneg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven. Cached: modAddRight] modMulRightNonneg
modMulRightNonneg :: TP Proof
modMulRightNonneg = do
   mAddL <- modAddLeft
   mAddR <- modAddRight

   induct "modMulRightNonneg"
      (\(Forall @"a" a) (Forall @"b" b) (Forall @"m" m) -> a .>= 0 .&& m .> 0 .=> (a*b) `sEMod` m .== (a * b `sEMod` m) `sEMod` m) $
      \ih a b m -> [a .>= 0, m .> 0] |- ((a+1)*b) `sEMod` m
                                     =: (a*b+b) `sEMod` m
                                     ?? mAddR `at` (Inst @"a" (a*b), Inst @"b" b, Inst @"m" m)
                                     =: (a*b + b `sEMod` m) `sEMod` m
                                     ?? mAddL `at` (Inst @"a" (a*b), Inst @"b" (b `sEMod` m), Inst @"m" m)
                                     =: ((a*b) `sEMod` m + b `sEMod` m) `sEMod` m
                                     ?? ih `at` (Inst @"b" b, Inst @"m" m)
                                     =: ((a * b `sEMod` m) `sEMod` m + b `sEMod` m) `sEMod` m
                                     ?? mAddL
                                     =: (a * b `sEMod` m + b `sEMod` m) `sEMod` m
                                     =: ((a+1) * b `sEMod` m) `sEMod` m
                                     =: qed

-- | \(a \geq 0 \land m > 0 \Rightarrow -ab \equiv -\left(a \cdot (b \bmod m)\right) \pmod{m}\)
--
-- >>> runCached modMulRightNeg
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Lemma: modSubRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: modMulRightNeg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven. Cached: modAddMultiple] modMulRightNeg
modMulRightNeg :: TP Proof
modMulRightNeg = do
   mAddL <- modAddLeft
   mSubR <- modSubRight

   induct "modMulRightNeg"
      (\(Forall @"a" a) (Forall @"b" b) (Forall @"m" m) -> a .>= 0 .&& m .> 0 .=> (-(a*b)) `sEMod` m .== (-(a * b `sEMod` m)) `sEMod` m) $
      \ih a b m -> [a .>= 0, m .> 0] |- (-((a+1)*b)) `sEMod` m
                                     =: (-(a*b)-b) `sEMod` m
                                     ?? mSubR `at` (Inst @"a" (-(a*b)), Inst @"b" b, Inst @"m" m)
                                     =: (-(a*b) - b `sEMod` m) `sEMod` m
                                     ?? mAddL `at` (Inst @"a" (-(a*b)), Inst @"b" (- (b `sEMod` m)), Inst @"m" m)
                                     =: ((-(a*b)) `sEMod` m - b `sEMod` m) `sEMod` m
                                     ?? ih `at` (Inst @"b" b, Inst @"m" m)
                                     =: ((-(a * b `sEMod` m)) `sEMod` m - b `sEMod` m) `sEMod` m
                                     ?? mAddL
                                     =: (-(a * b `sEMod` m) - b `sEMod` m) `sEMod` m
                                     =: (-((a+1) * b `sEMod` m)) `sEMod` m
                                     =: qed

-- | \(m > 0 \Rightarrow ab \equiv a \cdot (b \bmod m) \pmod{m}\)
--
-- >>> runCached modMulRight
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Inductive lemma: modMulRightNonneg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Cached: modAddLeft                      Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Lemma: modSubRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: modMulRightNeg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modMulRight
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven. Cached: modAddLeft, modAddMultiple, modAddRight] modMulRight
modMulRight :: TP Proof
modMulRight = do
   mMulNonneg <- modMulRightNonneg
   mMulNeg    <- modMulRightNeg

   calc "modMulRight"
        (\(Forall @"a" a) (Forall @"b" b) (Forall @"m" m) -> m .> 0 .=> (a*b) `sEMod` m .== (a * b `sEMod` m) `sEMod` m) $
        \a b m -> [m .> 0] |- cases [ a .>= 0 ==> (a*b) `sEMod` m
                                               ?? mMulNonneg `at` (Inst @"a" a, Inst @"b" b, Inst @"m" m)
                                               =: (a * b `sEMod` m) `sEMod` m
                                               =: qed
                                    , a .<  0 ==> (a*b) `sEMod` m
                                               =: (-((-a)*b)) `sEMod` m
                                               ?? mMulNeg `at` (Inst @"a" (-a), Inst @"b" b, Inst @"m" m)
                                               =: (-((-a) * b `sEMod` m)) `sEMod` m
                                               =: (a * b `sEMod` m) `sEMod` m
                                               =: qed
                                    ]

-- | \(m > 0 \Rightarrow ab \equiv (a \bmod m) \cdot b \pmod{m}\)
--
-- >>> runCached modMulLeft
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Inductive lemma: modMulRightNonneg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Cached: modAddLeft                      Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Lemma: modSubRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: modMulRightNeg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modMulRight
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modMulLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven. Cached: modAddLeft, modAddMultiple, modAddRight] modMulLeft
modMulLeft :: TP Proof
modMulLeft = do
   mMulR <- modMulRight

   calc "modMulLeft"
        (\(Forall @"a" a) (Forall @"b" b) (Forall @"m" m) -> m .> 0 .=> (a*b) `sEMod` m .== (a `sEMod` m * b) `sEMod` m) $
        \a b m -> [m .> 0] |- (a*b) `sEMod` m
                           =: (b*a) `sEMod` m
                           ?? mMulR
                           =: (b * a `sEMod` m) `sEMod` m
                           =: (a `sEMod` m * b) `sEMod` m
                           =: qed

-- | \(n \geq 0 \land m > 0 \Rightarrow b^n \equiv (b \bmod m)^n \pmod{m}\)
--
-- >>> runCached powerMod
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modAddLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Inductive lemma: modMulRightNonneg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Cached: modAddLeft                      Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Lemma: modSubRight
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: modMulRightNeg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modMulRight
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: modMulLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Cached: modAddLeft                      Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Cached: modMulRightNonneg               Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modAddRight                     Q.E.D.
-- Cached: modAddLeft                      Q.E.D.
-- Cached: modAddMultiple                  Q.E.D.
-- Cached: modSubRight                     Q.E.D.
-- Cached: modMulRightNeg                  Q.E.D.
-- Cached: modMulRight                     Q.E.D.
-- Inductive lemma: powerModInduct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: powerMod                         Q.E.D.
-- [Proven. Cached: modAddLeft, modAddMultiple, modAddRight, modMulRight] powerMod
powerMod :: TP Proof
powerMod = do
   mMulL <- modMulLeft
   mMulR <- modMulRight

   -- We want to write the b parameter first, but need to induct on n. So, this helper rearranges the parameters only.
   pMod <- induct "powerModInduct"
      (\(Forall @"n" n) (Forall @"m" m) (Forall @"b" b) -> n .>= 0 .&& m .> 0 .=> power b n `sEMod` m .== power (b `sEMod` m) n `sEMod` m) $
      \ih n m b -> [n .>= 0, m .> 0] |- power b (n+1) `sEMod` m
                                     =: (power b n * b) `sEMod` m
                                     ?? mMulL `at` (Inst @"a" (power b n), Inst @"b" b, Inst @"m" m)
                                     =: (power b n `sEMod` m * b) `sEMod` m
                                     ?? ih `at` (Inst @"m" m, Inst @"b" b)
                                     =: (power (b `sEMod` m) n `sEMod` m * b) `sEMod` m
                                     ?? mMulL `at` (Inst @"a" (power (b `sEMod` m) n), Inst @"b" b, Inst @"m" m)
                                     =: (power (b `sEMod` m) n * b) `sEMod` m
                                     ?? mMulR `at` (Inst @"a" (power (b `sEMod` m) n), Inst @"b" b, Inst @"m" m)
                                     =: (power (b `sEMod` m) n * b `sEMod` m) `sEMod` m
                                     =: power (b `sEMod` m) (n+1) `sEMod` m
                                     =: qed

   -- Same as above, just a more natural selection of variable order.
   lemma "powerMod"
         (\(Forall @"b" b) (Forall @"n" n) (Forall @"m" m) -> n .>= 0 .&& m .> 0 .=> power b n `sEMod` m .== power (b `sEMod` m) n `sEMod` m)
         [pMod]
