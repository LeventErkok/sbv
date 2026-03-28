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
-- We also demonstrate the use of recall for reusing previously established proofs.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.PowerMod where

import Data.SBV
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- | Power function over integers.
power :: SInteger -> SInteger -> SInteger
power = smtFunction "power" $ \b n -> [sCase| n of
                                         _ | n .<= 0 -> 1
                                         _           -> b * power b (n-1)
                                      |]

-- | \(m > 1 \Rightarrow n + mk \equiv n \pmod{m}\)
--
-- ==== __Proof__
-- >>> runTP modAddMultiple
-- Inductive lemma: modAddMultiple
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modAddMultiple :: Ɐk ∷ Integer → Ɐn ∷ Integer → Ɐm ∷ Integer → Bool
modAddMultiple :: TP (Proof (Forall "k" Integer -> Forall "n" Integer -> Forall "m" Integer -> SBool))
modAddMultiple = do
   inductWith cvc5 "modAddMultiple"
      (\(Forall k) (Forall n) (Forall m) -> m .> 1 .=> (n + m*k) `sEMod` m .== n `sEMod` m) $
      \ih k n m -> [m .> 1] |- (n + m*(k+1)) `sEMod` m
                              =: (n + m*k + m) `sEMod` m
                              =: (n + m*k) `sEMod` m
                              ?? ih `at` (Inst @"n" n, Inst @"m" m)
                              =: n `sEMod` m
                              =: qed

-- | \(m > 0 \Rightarrow a + b \equiv a + (b \bmod m) \pmod{m}\)
--
-- ==== __Proof__
-- >>> runTP modAddRight
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
-- [Proven] modAddRight :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐm ∷ Integer → Bool
modAddRight :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "m" Integer -> SBool))
modAddRight = do
   mAddMul <- modAddMultiple
   calc "modAddRight"
      (\(Forall a) (Forall b) (Forall m) -> m .> 0  .=>  (a+b) `sEMod` m .== (a + b `sEMod` m) `sEMod` m) $
      \a b m -> [m .> 0] |- (a+b) `sEMod` m
                         =: (a + b `sEMod` m + m * b `sEDiv` m) `sEMod` m
                         ?? mAddMul `at` (Inst @"k" (b `sEDiv` m), Inst @"n" (a + b `sEMod` m), Inst @"m" m)
                         =: (a + b `sEMod` m) `sEMod` m
                         =: qed

-- | \(m > 0 \Rightarrow a + b \equiv (a \bmod m) + b \pmod{m}\)
--
-- ==== __Proof__
-- >>> runTP modAddLeft
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
-- [Proven] modAddLeft :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐm ∷ Integer → Bool
modAddLeft :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "m" Integer -> SBool))
modAddLeft = do
   mAddR <- modAddRight
   calc "modAddLeft"
      (\(Forall a) (Forall b) (Forall m) -> m .> 0 .=>  (a+b) `sEMod` m .== (a `sEMod` m + b) `sEMod` m) $
      \a b m -> [m .> 0] |- (a+b) `sEMod` m
                         =: (b+a) `sEMod` m
                         ?? mAddR
                         =: (b + a `sEMod` m) `sEMod` m
                         =: (a `sEMod` m + b) `sEMod` m
                         =: qed

-- | \(m > 0 \Rightarrow a - b \equiv a - (b \bmod m) \pmod{m}\)
--
-- ==== __Proof__
-- >>> runTP modSubRight
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
-- [Proven] modSubRight :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐm ∷ Integer → Bool
modSubRight :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "m" Integer -> SBool))
modSubRight = do
   mAddMul <- modAddMultiple
   calc "modSubRight"
      (\(Forall a) (Forall b) (Forall m) -> m .> 0 .=>  (a-b) `sEMod` m .== (a - b `sEMod` m) `sEMod` m) $
      \a b m -> [m .> 0] |- (a - b) `sEMod` m
                         ?? b .== b `sEMod` m + m * b `sEDiv` m
                         =: (a - (b `sEMod` m + m * b `sEDiv` m)) `sEMod` m
                         =: ((a - b `sEMod` m) + m * (- (b `sEDiv` m))) `sEMod` m
                         ?? mAddMul `at` (Inst @"k" (- (b `sEDiv` m)), Inst @"n" (a - b `sEMod` m), Inst @"m" m)
                         =: (a - b `sEMod` m) `sEMod` m
                         =: qed

-- | \(a \geq 0 \land m > 0 \Rightarrow ab \equiv a \cdot (b \bmod m) \pmod{m}\)
--
-- ==== __Proof__
-- >>> runTP modMulRightNonneg
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
-- [Proven] modMulRightNonneg :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐm ∷ Integer → Bool
modMulRightNonneg :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "m" Integer -> SBool))
modMulRightNonneg = do
   mAddL <- modAddLeft
   mAddR <- recall modAddRight

   induct "modMulRightNonneg"
      (\(Forall a) (Forall b) (Forall m) -> a .>= 0 .&& m .> 0 .=> (a*b) `sEMod` m .== (a * b `sEMod` m) `sEMod` m) $
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
-- ==== __Proof__
-- >>> runTP modMulRightNeg
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
-- Lemma: modSubRight                      Q.E.D.
-- Inductive lemma: modMulRightNeg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modMulRightNeg :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐm ∷ Integer → Bool
modMulRightNeg :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "m" Integer -> SBool))
modMulRightNeg = do
   mAddL <- modAddLeft
   mSubR <- recall modSubRight

   induct "modMulRightNeg"
      (\(Forall a) (Forall b) (Forall m) -> a .>= 0 .&& m .> 0 .=> (-(a*b)) `sEMod` m .== (-(a * b `sEMod` m)) `sEMod` m) $
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
-- ==== __Proof__
-- >>> runTP modMulRight
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
-- Lemma: modMulRightNeg                   Q.E.D.
-- Lemma: modMulRight
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modMulRight :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐm ∷ Integer → Bool
modMulRight :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "m" Integer -> SBool))
modMulRight = do
   mMulNonneg <- modMulRightNonneg
   mMulNeg    <- recall modMulRightNeg

   calc "modMulRight"
        (\(Forall a) (Forall b) (Forall m) -> m .> 0 .=> (a*b) `sEMod` m .== (a * b `sEMod` m) `sEMod` m) $
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
-- ==== __Proof__
-- >>> runTP modMulLeft
-- Lemma: modMulRight                      Q.E.D.
-- Lemma: modMulLeft
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] modMulLeft :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐm ∷ Integer → Bool
modMulLeft :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "m" Integer -> SBool))
modMulLeft = do
   mMulR <- recall modMulRight

   calc "modMulLeft"
        (\(Forall a) (Forall b) (Forall m) -> m .> 0 .=> (a*b) `sEMod` m .== (a `sEMod` m * b) `sEMod` m) $
        \a b m -> [m .> 0] |- (a*b) `sEMod` m
                           =: (b*a) `sEMod` m
                           ?? mMulR
                           =: (b * a `sEMod` m) `sEMod` m
                           =: (a `sEMod` m * b) `sEMod` m
                           =: qed

-- | \(n \geq 0 \land m > 0 \Rightarrow b^n \equiv (b \bmod m)^n \pmod{m}\)
--
-- ==== __Proof__
-- >>> runTP powerMod
-- Lemma: modMulLeft                       Q.E.D.
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
-- Functions proven terminating: power
-- [Proven] powerMod :: Ɐb ∷ Integer → Ɐn ∷ Integer → Ɐm ∷ Integer → Bool
powerMod :: TP (Proof (Forall "b" Integer -> Forall "n" Integer -> Forall "m" Integer -> SBool))
powerMod = do
   mMulL <- recall modMulLeft
   mMulR <- recall modMulRight

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
         (\(Forall b) (Forall n) (Forall m) -> n .>= 0 .&& m .> 0 .=> power b n `sEMod` m .== power (b `sEMod` m) n `sEMod` m)
         [proofOf pMod]

-- | \(n \geq 0 \Rightarrow 1^n = 1\)
--
-- ==== __Proof__
-- >>> runTP onePower
-- Inductive lemma: onePower
--   Step: Base                            Q.E.D.
--   Step: 1 (unfold power)                Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: power
-- [Proven] onePower :: Ɐn ∷ Integer → Bool
onePower :: TP (Proof (Forall "n" Integer -> SBool))
onePower = induct "onePower"
                  (\(Forall n) -> n .>= 0 .=> power 1 n .== 1) $
                  \ih n -> [] |- power 1 (n+1)
                               ?? "unfold power"
                               =: 1 * power 1 n
                               ?? ih
                               =: (1 :: SInteger)
                               =: qed

-- | \(n \geq 0 \Rightarrow (27^n \bmod 13) = 1\)
--
-- ==== __Proof__
-- >>> runTP powerOf27
-- Lemma: onePower                         Q.E.D.
-- Lemma: powerMod                         Q.E.D.
-- Lemma: powerOf27
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: power
-- [Proven] powerOf27 :: Ɐn ∷ Integer → Bool
powerOf27 :: TP (Proof (Forall "n" Integer -> SBool))
powerOf27 = do
   pOne <- recall onePower
   pMod <- recall powerMod
   calc "powerOf27" (\(Forall n) -> n .>= 0 .=> power 27 n `sEMod` 13 .== 1) $
                    \n -> [n .>= 0]
                       |- power 27 n `sEMod` 13
                       ?? pMod `at` (Inst @"b" 27, Inst @"n" n, Inst @"m" 13)
                       =: power (27 `sEMod` 13) n `sEMod` 13
                       =: power 1 n `sEMod` 13
                       ?? pOne
                       =: 1 `sEMod` 13
                       =: (1 :: SInteger)
                       =: qed

-- | \(n \geq 0 \wedge m > 0 \implies (27^{\frac{n}{3}} \bmod 13) \cdot 3^{n \bmod 3} \equiv 3^{n \bmod 3} \pmod{m}\)
--
-- ==== __Proof__
-- >>> runTP powerOfThreeMod13VarDivisor
-- Lemma: powerOf27                        Q.E.D.
-- Lemma: powerOfThreeMod13VarDivisor
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: power
-- [Proven] powerOfThreeMod13VarDivisor :: Ɐn ∷ Integer → Ɐm ∷ Integer → Bool
powerOfThreeMod13VarDivisor :: TP (Proof (Forall "n" Integer -> Forall "m" Integer -> SBool))
powerOfThreeMod13VarDivisor = do
   p27 <- recall powerOf27
   calc "powerOfThreeMod13VarDivisor"
        (\(Forall n) (Forall m) ->
            n .>= 0 .&& m .> 0 .=>     power 27 (n `sEDiv` 3) `sEMod` 13 * power 3 (n `sEMod` 3) `sEMod` m
                                   .== power  3 (n `sEMod` 3) `sEMod` m) $
        \n m -> [n .>= 0, m .> 0]
             |- power 27 (n `sEDiv` 3) `sEMod` 13 * power 3 (n `sEMod` 3) `sEMod` m
             ?? p27 `at` Inst @"n" (sEDiv n 3)
             =: power 3 (n `sEMod` 3) `sEMod` m
             =: qed
