-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Peano
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Modeling Peano arithmetic in SBV and proving various properties using TP.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP               #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeAbstractions  #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Peano where

import Data.SBV
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- | Natural numbers. (If you are looking at the haddock documents, note the plethora of definitions
-- the call to 'mkSymbolic' generates. You can mostly ignore these, except for the case analyzer,
-- the testers and accessors.)
data Nat = Zero
         | Succ { prev :: Nat }

-- | Create a symbolic version of naturals.
mkSymbolic ''Nat

-- | Numeric instance. Choices: We clamp everything at 'Zero'. Negation is identity.
instance Num Nat where
  fromInteger i | i <= 0 = Zero
                | True   = Succ (fromInteger (i - 1))

  a + Zero   = a
  a + Succ b = Succ (a + b)

  Zero   - _      = Zero
  Succ a - Zero   = Succ a
  Succ a - Succ b = a - b

  _ * Zero   = Zero
  a * Succ b = a + a * b

  abs = id

  signum Zero = 0
  signum _    = 1

  negate = id

-- Symbolic numeric instance, mirroring the above
instance Num SNat where
  fromInteger = literal . fromInteger

  (+) = plus
      where plus = smtFunction "sNatPlus" $
                     \a b -> [sCase|Nat a of
                               Zero   -> b
                               Succ p -> sSucc (p + b)
                             |]

  (-) = subt
      where -- Quasi-quotes cannot be nested, so we have to have this explicit ite.
            subt = smtFunction "sNatSubtract" $
                     \a b -> ite (isZero a) sZero [sCase|Nat b of
                                                    Zero -> a
                                                    Succ p -> sprev a - p
                                                  |]

  (*) = times
      where times = smtFunction "sNatTimes" $
                      \a b -> [sCase|Nat a of
                                Zero   -> sZero
                                Succ p -> b + p * b
                              |]

  abs = id

  signum a = [sCase|Nat a of
               Zero -> 0
               _    -> 1
             |]

-- * Conversion to and from integers

-- | Convert from 'Nat' to 'Integer'.
--
-- NB. When writing the properties below, we use the notation \(\overline{n}\) to mean @n2i n@.
n2i :: SNat -> SInteger
n2i = smtFunction "n2i" $ \n -> [sCase|Nat n of
                                   Zero   -> 0
                                   Succ p -> 1 + n2i p
                                |]

-- | Convert Non-negative integers to 'Nat'. Negative numbers become 'Zero'.
--
-- NB. When writing the properties below, we use the notation \(\underline{i}\) to mean @i2n i@.
i2n :: SInteger -> SNat
i2n = smtFunction "i2n" $ \i -> ite (i .<= 0) sZero (sSucc (i2n (i - 1)))

-- | \(\overline{n} \geq 0\)
--
-- >>> runTP n2iNonNeg
-- Lemma: n2iNonNeg                        Q.E.D.
-- [Proven] n2iNonNeg :: Ɐn ∷ Nat → Bool
n2iNonNeg  :: TP (Proof (Forall "n" Nat -> SBool))
n2iNonNeg = inductiveLemma "n2iNonNeg" (\(Forall n) -> n2i n .>= 0) []

-- | \(i \geq 0 \;\Rightarrow\; \overline{\underline{i}} = i\).
--
-- >>> runTP i2n2i
-- Lemma: i2n2i                            Q.E.D.
-- [Proven] i2n2i :: Ɐi ∷ Integer → Bool
i2n2i :: TP (Proof (Forall "i" Integer -> SBool))
i2n2i = inductiveLemma "i2n2i" (\(Forall i) -> i .>= 0 .=> n2i (i2n i) .== i) []

-- | \(\underline{\overline{n}} = n\)
--
-- >>> runTP n2i2n
-- Lemma: n2i2n                            Q.E.D.
-- [Proven] n2i2n :: Ɐn ∷ Nat → Bool
n2i2n :: TP (Proof (Forall "n" Nat -> SBool))
n2i2n = inductiveLemma "n2i2n" (\(Forall n) -> i2n (n2i n) .== n) []

-- * Correctness of addition

-- | \(\overline{m + n} = \overline{m} + \overline{n}\)
--
-- >>> runTP addCorrect
-- Lemma: addCorrect                       Q.E.D.
-- [Proven] addCorrect :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
addCorrect :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
addCorrect = inductiveLemma "addCorrect"
                            (\(Forall m) (Forall n) -> n2i (m + n) .== n2i m + n2i n)
                            []

-- * Correctness of multiplication

-- | \(\overline{m * n} = \overline{m} * \overline{n}\)
--
-- >>> runTP mulCorrect
-- Lemma: caseZero                         Q.E.D.
-- Lemma: addCorrect                       Q.E.D.
-- Lemma: caseSucc
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6 (defn of n2i)                 Q.E.D.
--   Step: 7                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: mulCorrect                       Q.E.D.
-- [Proven] mulCorrect :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
mulCorrect :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
mulCorrect = do
    caseZero <- inductiveLemma
                  "caseZero"
                  (\(Forall @"n" n) -> n2i (sZero * n) .== n2i sZero * n2i n)
                  []

    add <- recall "addCorrect" addCorrect

    caseSucc <- calc "caseSucc"
                      (\(Forall @"m" m) (Forall @"n" n) ->
                            n2i (m * n) .== n2i m * n2i n .=> n2i (sSucc m * n) .== n2i (sSucc m) * n2i n) $
                      \m n -> let ih = n2i (m * n) .== n2i m * n2i n
                           in [ih] |- n2i (sSucc m * n)
                                   =: n2i (n + m * n)
                                   ?? add `at` (Inst @"m" n, Inst @"n" (m * n))
                                   =: n2i n + n2i (m * n)
                                   ?? ih
                                   =: n2i n + n2i m * n2i n
                                   =: n2i n + n2i n * n2i m
                                   =: n2i n * (1 + n2i m)
                                   ?? "defn of n2i"
                                   =: n2i n * n2i (sSucc m)
                                   =: n2i (sSucc m) * n2i n
                                   =: qed

    inductiveLemma
       "mulCorrect"
       (\(Forall m) (Forall n) -> n2i (m * n) .== n2i m * n2i n)
       [proofOf caseZero, proofOf caseSucc]

-- Prove 15 theorems in: https://en.wikipedia.org/wiki/Peano_axioms
