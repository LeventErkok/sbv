-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Peano
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Modeling Peano arithmetic in SBV and proving various properties using TP.
-- Most of the properties we prove come from <https://en.wikipedia.org/wiki/Peano_axioms>.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

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
         deriving (Eq, Ord)

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
                     \a b -> ite (isZero a) 0 [sCase|Nat b of
                                                 Zero -> a
                                                 Succ p -> sprev a - p
                                              |]

  (*) = times
      where times = smtFunction "sNatTimes" $
                      \a b -> [sCase|Nat a of
                                Zero   -> 0
                                Succ p -> b + p * b
                              |]

  abs = id

  signum a = [sCase|Nat a of
               Zero -> 0
               _    -> 1
             |]

-- | Symbolic ordering. We only define less-than, other methods use the defaults.
instance OrdSymbolic SNat where
   m .< n = quantifiedBool (\(Exists k) -> n .== m + sSucc k)

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
i2n = smtFunction "i2n" $ \i -> ite (i .<= 0) 0 (sSucc (i2n (i - 1)))

-- | \(\overline{n} \geq 0\)
--
-- >>> runTP n2iNonNeg
-- Lemma: n2iNonNeg                        Q.E.D.
-- [Proven] n2iNonNeg :: Ɐn ∷ Nat → Bool
n2iNonNeg  :: TP (Proof (Forall "n" Nat -> SBool))
n2iNonNeg = inductiveLemma "n2iNonNeg" (\(Forall n) -> n2i n .>= 0) []

-- | \(\overline{\underline{i}} = \max(i, 0)\).
--
-- >>> runTP i2n2i
-- Lemma: i2n2i                            Q.E.D.
-- [Proven] i2n2i :: Ɐi ∷ Integer → Bool
i2n2i :: TP (Proof (Forall "i" Integer -> SBool))
i2n2i = inductiveLemma "i2n2i" (\(Forall i) -> n2i (i2n i) .== i `smax` 0) []

-- | \(\underline{\overline{n}} = n\)
--
-- >>> runTP n2i2n
-- Lemma: n2i2n                            Q.E.D.
-- [Proven] n2i2n :: Ɐn ∷ Nat → Bool
n2i2n :: TP (Proof (Forall "n" Nat -> SBool))
n2i2n = inductiveLemma "n2i2n" (\(Forall n) -> i2n (n2i n) .== n) []

-- | \(\overline{m + n} = \overline{m} + \overline{n}\)
--
-- >>> runTP n2iAdd
-- Lemma: n2iAdd                           Q.E.D.
-- [Proven] n2iAdd :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
n2iAdd :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
n2iAdd = inductiveLemma "n2iAdd" (\(Forall m) (Forall n) -> n2i (m + n) .== n2i m + n2i n) []

-- * Addition

-- ** Correctness

-- | \(\overline{m + n} = \overline{m} + \overline{n}\)
--
-- >>> runTP addCorrect
-- Lemma: addCorrect                       Q.E.D.
-- [Proven] addCorrect :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
addCorrect :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
addCorrect = inductiveLemma
               "addCorrect"
               (\(Forall m) (Forall n) -> n2i (m + n) .== n2i m + n2i n)
               []

-- ** Left and right unit

-- | \(0 + m = m\)
--
-- >>> runTP addLeftUnit
-- Lemma: addLeftUnit                      Q.E.D.
-- [Proven] addLeftUnit :: Ɐm ∷ Nat → Bool
addLeftUnit :: TP (Proof (Forall "m" Nat -> SBool))
addLeftUnit = lemma "addLeftUnit" (\(Forall m) -> 0 + m .== m) []

-- | \(m + 0 = m\)
--
-- >>> runTP addRightUnit
-- Lemma: addRightUnit                     Q.E.D.
-- [Proven] addRightUnit :: Ɐm ∷ Nat → Bool
addRightUnit :: TP (Proof (Forall "m" Nat -> SBool))
addRightUnit = inductiveLemma "addRightUnit" (\(Forall m) -> m + 0 .== m) []

-- ** Addition with non-zero values

-- | \(m + \mathrm{Succ}\,n = \mathrm{Succ}\,(m + n)\)
--
-- >>> runTP addSucc
-- Lemma: caseZero                         Q.E.D.
-- Lemma: caseSucc
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: addSucc                          Q.E.D.
-- [Proven] addSucc :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
addSucc :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
addSucc = do
   caseZero <- lemma "caseZero"
                      (\(Forall @"n" n) -> 0 + sSucc n .== sSucc (0 + n))
                      []

   caseSucc <- calc "caseSucc"
                    (\(Forall @"m" m) (Forall @"n" n) ->
                        m + sSucc n .== sSucc (m + n) .=> sSucc m + sSucc n .== sSucc (sSucc m + n)) $
                    \m n -> let ih = m + sSucc n .== sSucc (m + n)
                         in [ih] |- sSucc m + sSucc n
                                 =: sSucc (m + sSucc n)
                                 ?? ih
                                 =: sSucc (sSucc (m + n))
                                 =: sSucc (sSucc m + n)
                                 =: qed

   inductiveLemma
      "addSucc"
      (\(Forall @"m" m) (Forall @"n" n) -> m + sSucc n .== sSucc (m + n))
      [proofOf caseZero, proofOf caseSucc]

-- ** Associativity

-- | \(m + (n + o) = (m + n) + o\)
--
-- >>> runTP addAssoc
-- Lemma: addAssoc                         Q.E.D.
-- [Proven] addAssoc :: Ɐm ∷ Nat → Ɐn ∷ Nat → Ɐo ∷ Nat → Bool
addAssoc :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> Forall "o" Nat -> SBool))
addAssoc = inductiveLemma
             "addAssoc"
             (\(Forall m) (Forall n) (Forall o) -> m + (n + o) .== (m + n) + o)
             []

-- ** Commutativity

-- | \(m + n = n + m\)
--
-- >>> runTP addComm
-- Lemma: addLeftUnit                      Q.E.D.
-- Lemma: addRightUnit                     Q.E.D.
-- Lemma: caseZero                         Q.E.D.
-- Lemma: addSucc                          Q.E.D.
-- Lemma: caseSucc
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: addComm                          Q.E.D.
-- [Proven] addComm :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
addComm :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
addComm = do
    alu <- recall "addLeftUnit"  addLeftUnit
    aru <- recall "addRightUnit" addRightUnit

    caseZero <- lemma "caseZero"
                      (\(Forall @"n" (n :: SNat)) -> 0 + n .== n + 0)
                      [proofOf alu, proofOf aru]

    as <- recall "addSucc" addSucc

    caseSucc <- calc "caseSucc"
                     (\(Forall @"m" m) (Forall @"n" n) -> m + n .== n + m .=> sSucc m + n .== n + sSucc m) $
                     \m n -> let ih = m + n .== n + m
                          in [ih] |- sSucc m + n
                                  =: sSucc (m + n)
                                  ?? ih
                                  =: sSucc (n + m)
                                  ?? as `at` (Inst @"m" n, Inst @"n" m)
                                  =: n + sSucc m
                                  =: qed

    inductiveLemma "addComm"
                   (\(Forall m) (Forall n) -> m + n .== n + m)
                   [proofOf caseZero, proofOf caseSucc]

-- * Multiplication

-- ** Correctness

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
--   Result:                               Q.E.D.
-- Lemma: mullCorrect                      Q.E.D.
-- [Proven] mullCorrect :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
mulCorrect :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
mulCorrect = do
   caseZero <- lemma "caseZero"
                     (\(Forall @"n" n) -> n2i (0 * n) .== n2i 0 * n2i n)
                     []

   addC <- recall "addCorrect" addCorrect

   caseSucc <- calc "caseSucc"
                    (\(Forall @"m" m) (Forall @"n" n) ->
                          n2i (m * n) .== n2i m * n2i n .=> n2i (sSucc m * n) .== n2i (sSucc m) * n2i n) $
                    \m n -> let ih = n2i (m * n) .== n2i m * n2i n
                         in [ih] |- n2i (sSucc m * n)
                                 =: n2i (n + m * n)
                                 ?? addC `at` (Inst @"m" n, Inst @"n" (m * n))
                                 =: n2i n + n2i (m * n)
                                 ?? ih
                                 =: n2i n + n2i m * n2i n
                                 =: n2i n * (1 + n2i m)
                                 =: n2i n * n2i (sSucc m)
                                 =: qed

   inductiveLemma
       "mullCorrect"
       (\(Forall @"m" m) (Forall @"n" n) -> n2i (m * n) .== n2i m * n2i n)
       [proofOf caseZero, proofOf caseSucc]

-- ** Left and right absorption

-- | \(0 * m = 0\)
--
-- >>> runTP mulLeftAbsorb
-- Lemma: mulLeftAbsorb                    Q.E.D.
-- [Proven] mulLeftAbsorb :: Ɐm ∷ Nat → Bool
mulLeftAbsorb :: TP (Proof (Forall "m" Nat -> SBool))
mulLeftAbsorb = lemma "mulLeftAbsorb" (\(Forall m) -> 0 * m .== 0) []

-- | \(m * 0 = 0\)
--
-- >>> runTP mulRightAbsorb
-- Lemma: mulRightAbsorb                   Q.E.D.
-- [Proven] mulRightAbsorb :: Ɐm ∷ Nat → Bool
mulRightAbsorb :: TP (Proof (Forall "m" Nat -> SBool))
mulRightAbsorb = inductiveLemma "mulRightAbsorb" (\(Forall m) -> m * 0 .== 0) []

-- ** Left and right unit

-- | \(\mathrm{Succ\,0} * m = m\)
--
-- >>> runTP mulLeftUnit
-- Lemma: mulLeftUnit                      Q.E.D.
-- [Proven] mulLeftUnit :: Ɐm ∷ Nat → Bool
mulLeftUnit :: TP (Proof (Forall "m" Nat -> SBool))
mulLeftUnit = inductiveLemma "mulLeftUnit" (\(Forall m) -> sSucc 0 * m .== m) []

-- | \(m * \mathrm{Succ\,0} = m\)
--
-- >>> runTP mulRightUnit
-- Lemma: mulRightUnit                     Q.E.D.
-- [Proven] mulRightUnit :: Ɐm ∷ Nat → Bool
mulRightUnit :: TP (Proof (Forall "m" Nat -> SBool))
mulRightUnit = inductiveLemma "mulRightUnit" (\(Forall m) -> m * sSucc 0 .== m) []

-- ** Distribution over addition

-- | \(m * (n + o) = m * n + m * o\)
--
-- >>> runTP distribLeft
-- Lemma: caseZero                         Q.E.D.
-- Lemma: addAssoc                         Q.E.D.
-- Lemma: addComm                          Q.E.D.
-- Lemma: caseSucc
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Step: 8                               Q.E.D.
--   Step: 9                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: distribLeft                      Q.E.D.
-- [Proven] distribLeft :: Ɐm ∷ Nat → Ɐn ∷ Nat → Ɐo ∷ Nat → Bool
distribLeft :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> Forall "o" Nat -> SBool))
distribLeft = do
   caseZero <- lemma "caseZero" (\(Forall @"n" n) (Forall @"o" (o :: SNat)) -> 0 * (n + o) .== 0 * n + 0 * o) []

   addAsc <- recall "addAssoc" addAssoc
   addCom <- recall "addComm"  addComm

   caseSucc <- calc "caseSucc"
                    (\(Forall @"m" m) (Forall @"n" n) (Forall @"o" o) ->
                        m * (n + o) .== m * n + m * o .=> sSucc m * (n + o) .== sSucc m * n + sSucc m * o) $
               \m n o -> let ih = m * (n + o) .== m * n + m * o
                      in [ih] |- sSucc m * (n + o)
                              =: (n + o) + m * (n + o)
                              ?? ih
                              =: (n + o) + (m * n + m * o)
                              ?? addAsc `at` (Inst @"m" n, Inst @"n" o, Inst @"o" (m * n + m * o))
                              =: n + (o + (m * n + m * o))
                              ?? addCom `at` (Inst @"m" (m * n), Inst @"n" (m * o))
                              =: n + (o + (m * o + m * n))
                              ?? addAsc `at` (Inst @"m" o, Inst @"n" (m * o), Inst @"o" (m * n))
                              =: n + ((o + m * o) + m * n)
                              =: n + (sSucc m * o + m * n)
                              ?? addCom `at` (Inst @"m" (sSucc m * o), Inst @"n" (m * n))
                              =: n + (m * n + sSucc m * o)
                              ?? addAsc `at` (Inst @"m" n, Inst @"n" (m * n), Inst @"o" (sSucc m * o))
                              =: (n + m * n) + sSucc m * o
                              =: sSucc m * n + sSucc m * o
                              =: qed

   inductiveLemma
     "distribLeft"
     (\(Forall m) (Forall n) (Forall o) -> m * (n + o) .== m * n + m * o)
     [proofOf caseZero, proofOf caseSucc]

-- | \((m + n) * o = m * o + n * o\)
--
-- >>> runTP distribRight
-- Lemma: caseZero                         Q.E.D.
-- Lemma: addAssoc                         Q.E.D.
-- Lemma: addComm                          Q.E.D.
-- Lemma: addSucc                          Q.E.D.
-- Lemma: caseSucc
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: distribRight                     Q.E.D.
-- [Proven] distribRight :: Ɐm ∷ Nat → Ɐn ∷ Nat → Ɐo ∷ Nat → Bool
distribRight :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> Forall "o" Nat -> SBool))
distribRight = do
   caseZero <- lemma "caseZero" (\(Forall @"n" n) (Forall @"o" (o :: SNat)) -> (0 + n) * o .== 0 * o + n * o) []

   pAddAssoc <- recall "addAssoc" addAssoc
   pAddCom   <- recall "addComm"  addComm
   pAddSucc  <- recall "addSucc"  addSucc

   caseSucc <- calc "caseSucc"
                    (\(Forall @"m" m) (Forall @"n" n) (Forall @"o" o) ->
                        (m + n) * o .== m * o + n * o .=> (sSucc m + n) * o .== sSucc m * o + n * o) $
               \m n o -> let ih = (m + n) * o .== m * o + n * o
                      in [ih] |- (sSucc m + n) * o
                              ?? pAddCom `at` (Inst @"m" (sSucc m), Inst @"n" n)
                              =: (n + sSucc m) * o
                              ?? pAddSucc `at` (Inst @"m" n, Inst @"n" m)
                              =: sSucc (n + m) * o
                              ?? pAddCom `at` (Inst @"m" n, Inst @"n" m)
                              =: sSucc (m + n) * o
                              =: o + (m + n) * o
                              ?? ih
                              =: o + (m * o + n *o)
                              ?? pAddAssoc `at` (Inst @"m" o, Inst @"n" (m * o), Inst @"o" (n * o))
                              =: (o + m * o) + n * o
                              =: sSucc m * o + n * o
                              =: qed

   inductiveLemma
     "distribRight"
     (\(Forall m) (Forall n) (Forall o) -> (m + n) * o .== m * o + n * o)
     [proofOf caseZero, proofOf caseSucc]

-- ** Multiplication with non-zero values

-- | \(m * \mathrm{Succ}\,n = m * n + m\)
--
-- >>> runTP mulSucc
-- Lemma: addLeftUnit                      Q.E.D.
-- Lemma: distribLeft                      Q.E.D.
-- Lemma: mulRightUnit                     Q.E.D.
-- Lemma: addComm                          Q.E.D.
-- Lemma: mulSucc
--   Step: 1                               Q.E.D.
--   Step: 2 (defn of +)                   Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mulSucc :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
mulSucc :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
mulSucc = do
   alu <- recall "addLeftUnit"    addLeftUnit
   dL  <- recall "distribLeft"    distribLeft
   mru <- recall "mulRightUnit"   mulRightUnit
   ac  <- recall "addComm"        addComm

   calc "mulSucc"
        (\(Forall @"m" m) (Forall @"n" n) -> m * sSucc n .== m * n + m) $
        \m n -> [] |- m * sSucc n
                   ?? alu
                   =: m * sSucc (0 + n)
                   ?? "defn of +"
                   =: m * (sSucc 0 + n)
                   ?? dL `at` (Inst @"m" m, Inst @"n" (sSucc 0), Inst @"o" n)
                   =: m * sSucc 0 + m * n
                   ?? mru
                   =: m + m * n
                   ?? ac `at` (Inst @"m" m, Inst @"n" (m * n))
                   =: m * n + m
                   =: qed

-- ** Associativity

-- | \(m * (n * o) = (m * n) * o\)
--
-- >>> runTP mulAssoc
-- Lemma: caseZero                         Q.E.D.
-- Lemma: distribRight                     Q.E.D.
-- Lemma: caseSucc
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: mulAssoc                         Q.E.D.
-- [Proven] mulAssoc :: Ɐm ∷ Nat → Ɐn ∷ Nat → Ɐo ∷ Nat → Bool
mulAssoc :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> Forall "o" Nat -> SBool))
mulAssoc = do
   caseZero <- lemma "caseZero"
                     (\(Forall @"n" n) (Forall @"o" (o :: SNat)) -> 0 * (n * o) .== (0 * n) * o)
                     []

   distR <- recall "distribRight" distribRight

   caseSucc <- calc "caseSucc"
                    (\(Forall @"m" m) (Forall @"n" n) (Forall @"o" o) ->
                       m * (n * o) .== (m * n) * o .=> sSucc m * (n * o) .== (sSucc m * n) * o) $
                    \m n o -> let ih = m * (n * o) .== (m * n) * o
                              in [ih] |- sSucc m * (n * o)
                                      =: (n * o) + m * (n * o)
                                      ?? ih
                                      =: (n * o) + (m * n) * o
                                      ?? distR `at` (Inst @"m" n, Inst @"n" (m * n), Inst @"o" o)
                                      =: (n + m * n) * o
                                      =: (sSucc m * n) * o
                                      =: qed

   inductiveLemma
     "mulAssoc"
     (\(Forall m) (Forall n) (Forall o) -> m * (n * o) .== (m * n) * o)
     [proofOf caseZero, proofOf caseSucc]

-- ** Commutativity

-- | \(m * n = n * m\)
--
-- >>> runTP mulComm
-- Lemma: mulRightAbsorb                   Q.E.D.
-- Lemma: caseZero                         Q.E.D.
-- Lemma: mulRightUnit                     Q.E.D.
-- Lemma: distribLeft                      Q.E.D.
-- Lemma: caseSucc
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: mulComm                          Q.E.D.
-- [Proven] mulComm :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
mulComm :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
mulComm = do
  mra <- recall "mulRightAbsorb" mulRightAbsorb

  caseZero <- lemma "caseZero"
                    (\(Forall @"m" (m :: SNat)) -> 0 * m .== m * 0)
                    [proofOf mra]

  mru <- recall "mulRightUnit" mulRightUnit
  dL  <- recall "distribLeft"  distribLeft

  caseSucc <- calc "caseSucc"
                   (\(Forall @"m" m) (Forall @"n" n) -> m * n .== n * m .=> sSucc m * n .== n * sSucc m) $
                   \m n -> let ih = m * n .== n * m
                        in [ih] |- sSucc m * n
                                =: n + m * n
                                ?? ih
                                =: n + n * m
                                ?? mru
                                =: n * sSucc 0 + n * m
                                ?? dL `at` (Inst @"m" n, Inst @"n" (sSucc 0), Inst @"o" m)
                                =: n * (sSucc 0 + m)
                                =: n * sSucc (0 + m)
                                =: n * sSucc m
                                =: qed

  inductiveLemma
    "mulComm"
    (\(Forall @"m" m) (Forall @"n" n) -> m * n .== n * m)
    [proofOf caseZero, proofOf caseSucc]

-- * Ordering

-- ** Transitivity of @<@

-- | \(m < n \;\wedge\; n < o \;\rightarrow\; m < o\)
--
-- >>> runTP ltTrans
-- Lemma: addAssoc                         Q.E.D.
-- Lemma: ltTrans
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] ltTrans :: Ɐm ∷ Nat → Ɐn ∷ Nat → Ɐo ∷ Nat → Bool
ltTrans :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> Forall "o" Nat -> SBool))
ltTrans = do
  aa <- recall "addAssoc" addAssoc

  calc "ltTrans"
       (\(Forall @"m" m) (Forall @"n" n) (Forall @"o" o) -> m .< n .&& n .< o .=> m .< o) $
       \m n o ->  [m .< n, n .< o]
              |-> let k1 = some "k1" (\k -> n .== m + sSucc k)
                      k2 = some "k2" (\k -> o .== n + sSucc k)
               in n .== m + sSucc k1
               =: o .== n + sSucc k2
               =: o .== (m + sSucc k1) + sSucc k2
               ?? aa `at` (Inst @"m" m, Inst @"n" (sSucc k1), Inst @"o" (sSucc k2))
               =: o .== m + (sSucc k1 + sSucc k2)
               =: o .== m + (sSucc (k1 + sSucc k2))
               =: m .< o
               =: sTrue
               =: qed

-- ** Irreflexivity of @<@

-- | \(\neg(m < m)\)
--
-- >>> runTP ltIrreflexive
-- Lemma: cancel                           Q.E.D.
-- Lemma: ltIrreflexive
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] ltIrreflexive :: Ɐm ∷ Nat → Bool
ltIrreflexive :: TP (Proof (Forall "m" Nat -> SBool))
ltIrreflexive = do
  cancel <- inductiveLemma
              "cancel"
              (\(Forall @"m" m) (Forall @"n" n) -> m + n .== m .=> n .== 0)
              []

  calc "ltIrreflexive"
       (\(Forall @"m" m) -> sNot (m .< m)) $
       \m -> [m .< m] |-> let k = some "k" (\d -> m .== m + sSucc d)
                      in m .== m + sSucc k
                      ?? cancel `at` (Inst @"m" m, Inst @"n" (sSucc k))
                      =: sSucc k .== 0
                      =: contradiction

-- ** Trichotomy

-- | \(m \geq n = \overline{m} \geq \overline{n}\)
--
-- >>> runTP lteEquiv
-- Lemma: n2iAdd                           Q.E.D.
-- Lemma: n2iNonNeg                        Q.E.D.
-- Lemma: n2i2n                            Q.E.D.
-- Lemma: i2n2i                            Q.E.D.
-- Lemma: addRightUnit                     Q.E.D.
-- Lemma: lteEquiv_ltr
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: lteEquiv_rtl
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7 (2 way case split)
--     Step: 7.1                           Q.E.D.
--     Step: 7.2.1                         Q.E.D.
--     Step: 7.2.2                         Q.E.D.
--     Step: 7.2.3                         Q.E.D.
--     Step: 7.2.4                         Q.E.D.
--     Step: 7.2.5                         Q.E.D.
--     Step: 7.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: lteEquiv                         Q.E.D.
-- [Proven] lteEquiv :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
lteEquiv :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
lteEquiv = do
    n2ia    <- recall "n2iAdd"       n2iAdd
    nn      <- recall "n2iNonNeg"    n2iNonNeg
    n2i2nId <- recall "n2i2n"        n2i2n
    i2n2iId <- recall "i2n2i"        i2n2i
    aru     <- recall "addRightUnit" addRightUnit

    ltr <- calcWith cvc5 "lteEquiv_ltr"
              (\(Forall @"m" m) (Forall @"n" n) -> (m .>= n) .=> (n2i m .>= n2i n)) $
              \m n -> [m .>= n]
                   |- n2i m .>= n2i n
                    =: cases [ m .== n ==> trivial
                             , m .>  n ==> let k = some "k" (\d -> m .== n + sSucc d)
                                        in n2i m .>= n2i n
                                        ?? m .> n
                                        =: n2i (n + sSucc k) .>= n2i n
                                        ?? n2ia `at` (Inst @"m" n, Inst @"n" (sSucc k))
                                        =: n2i n + n2i (sSucc k) .>= n2i n
                                        ?? nn `at` (Inst @"n" (sSucc k))
                                        =: sTrue
                                        =: qed
                             ]

    rtl <- calc "lteEquiv_rtl"
                (\(Forall @"m" m) (Forall @"n" n) -> (n2i m .>= n2i n) .=> (m .>= n)) $
                \m n -> [n2i m .>= n2i n]
                     |-> let k = n2i m - n2i n
                     in k .>= 0
                     =: n2i m .== n2i n + k
                     ?? i2n2iId `at` (Inst @"i" k)
                     =: n2i m .== n2i n + n2i (i2n k)
                     ?? n2ia `at` (Inst @"m" n, Inst @"n" (i2n k))
                     =: n2i m .== n2i (n + i2n k)
                     =: i2n (n2i m) .== i2n (n2i (n + i2n k))
                     ?? n2i2nId `at` Inst @"n" m
                     =: m .== i2n (n2i (n + i2n k))
                     ?? n2i2nId `at` Inst @"n" (n + i2n k)
                     =: m .== n + i2n k
                     =: cases [ k .>  0 ==> trivial
                              , k .<= 0 ==> m .== n + i2n k
                                         ?? i2n k .== 0
                                         =: m .== n + 0
                                         ?? aru
                                         =: m .== n
                                         =: m .== n .|| m .> n
                                         =: m .>= n
                                         =: qed
                              ]

    lemma "lteEquiv"
          (\(Forall m) (Forall n) -> (n2i m .>= n2i n) .== (m .>= n))
          [proofOf ltr, proofOf rtl]

-- | \(m \geq n \;\lor\; n \geq m\)
--
-- >>> runTP ordered
-- Lemma: lteEquiv                         Q.E.D.
-- Lemma: ordered
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] ordered :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
ordered :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
ordered = do
   lteEq <- recall "lteEquiv" lteEquiv

   calcWith cvc5 "ordered"
        (\(Forall m) (Forall n) -> m .>= n .|| n .>= m) $
        \m n -> [] |- (m .>= n .|| n .>= m)
                   ?? lteEq `at` (Inst @"m" m, Inst @"n" n)
                   =: (n2i m .>= n2i n .|| n .>= m)
                   ?? lteEq `at` (Inst @"m" n, Inst @"n" m)
                   =: (n2i m .>= n2i n .|| n2i n .>= n2i m)
                   =: qed

-- | \(m < n \;\lor\; m = n \;\lor\; n < m\)
--
-- >>> runTP trichotomy
-- Lemma: ordered                          Q.E.D.
-- Lemma: trichotomy                       Q.E.D.
-- [Proven] trichotomy :: Ɐm ∷ Nat → Ɐn ∷ Nat → Bool
trichotomy :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> SBool))
trichotomy = do
   pOrdered <- recall "ordered" ordered

   lemma "trichotomy"
         (\(Forall m) (Forall n) -> m .< n .|| m .== n .|| n .< m)
         [proofOf pOrdered]

-- ** Addition and ordering

-- | \(m < n \;\rightarrow\; m + o < n + o\)
--
-- >>> runTP addOrder
-- Lemma: addAssoc                         Q.E.D.
-- Lemma: addComm                          Q.E.D.
-- Lemma: addOrder
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] addOrder :: Ɐm ∷ Nat → Ɐn ∷ Nat → Ɐo ∷ Nat → Bool
addOrder :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> Forall "o" Nat -> SBool))
addOrder = do
  pAddAssoc <- recall "addAssoc" addAssoc
  pAddComm  <- recall "addComm"  addComm

  calc "addOrder"
       (\(Forall m) (Forall n) (Forall o) -> m .< n .=> m + o .< n + o) $
       \m n o -> [m .< n]
              |-> let k = some "k" (\d -> n .== m + sSucc d)
               in n .== m + sSucc k
               =: n + o .== (m + sSucc k) + o
               ?? pAddAssoc `at` (Inst @"m" m, Inst @"n" (sSucc k), Inst @"o" o)
               =: n + o .== m + (sSucc k + o)
               ?? pAddComm `at` (Inst @"m" (sSucc k), Inst @"n" o)
               =: n + o .== m + (o + sSucc k)
               ?? pAddAssoc `at` (Inst @"m" m, Inst @"n" o, Inst @"o" (sSucc k))
               =: n + o .== (m + o) + sSucc k
               =: m + o .<= n + o
               =: qed

-- ** Multiplication and ordering

-- | \(o > 0 \;\wedge\; m < n \;\rightarrow\; m * o < n * o\)
--
-- >>> runTP mulOrder
-- Lemma: distribRight                     Q.E.D.
-- Lemma: mulOrder
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mulOrder :: Ɐm ∷ Nat → Ɐn ∷ Nat → Ɐo ∷ Nat → Bool
mulOrder :: TP (Proof (Forall "m" Nat -> Forall "n" Nat -> Forall "o" Nat -> SBool))
mulOrder = do
  pDistribRight <- recall "distribRight" distribRight

  calc "mulOrder"
       (\(Forall m) (Forall n) (Forall o) -> 0 .< o .&& m .< n .=> m * o .< n * o) $
       \m n o -> [0 .< o, m .< n]
              |-> let k = some "k" (\d -> n .== m + sSucc d)
               in n .== m + sSucc k
               =: n * o .== (m + sSucc k) * o
               ?? pDistribRight `at` (Inst @"m" m, Inst @"n" (sSucc k), Inst @"o" o)
               =: n * o .== m * o + sSucc k * o
               ?? 0 .< o
               =: n * o .== m * o + sSucc k * sSucc (sprev o)
               =: n * o .== m * o + (sSucc (sprev o) + k * sSucc (sprev o))
               =: n * o .== m * o + sSucc (sprev o + k * sSucc (sprev o))
               =: m * o .< n * o
               =: qed

{-
https://en.wikipedia.org/wiki/Peano_axioms

13.   from wiki
14.   from wiki
15.   from wiki
16.   correctness of subtraction
17.   subtraction related props. with zero at least; follow add props
18.   exponentiation. correctness.
19.   factorial. correctness.
-}
