-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Ackermann
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving the relationship between Ackermann's original 3-argument function (1928)
-- and the Ackermann-Péter function (1935).
--
-- Ackermann's original function was a 3-argument function designed to demonstrate
-- a total computable function that is not primitive recursive. The third argument
-- generalizes the operation: @ack 0 n a = n + a@ (addition), and higher levels
-- correspond to multiplication, exponentiation, etc.
--
-- Rózsa Péter simplified this to a 2-argument function in 1935, which is what
-- most people today call "the Ackermann function."
--
-- This example is inspired by: <https://github.com/imandra-ai/imandrax-examples/blob/main/src/ackermann.iml>
--
-- Note: This proof was developed by Claude (Anthropic's AI assistant) with
-- minimal user prompting and guidance.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP               #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Ackermann where

import Data.SBV
import Data.SBV.Tuple
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Ackermann's original 3-argument function (1928)

-- | Ackermann's original 3-argument function (1928). This is the lesser-known
-- original version, not the commonly referenced Ackermann-Péter function.
-- The third argument @a@ generalizes the operation at each level.
ack :: SInteger -> SInteger -> SInteger -> SInteger
ack = smtFunction "ack" $ \m n a ->
    ite (m .<= 0) (n + a)
  $ ite (n .<= 0) 0
  $ ite (n .== 1) a
  $ ack (m - 1) (ack m (n - 1) a) a

-- * Ackermann-Péter function (1935)

-- | The Ackermann-Péter function (1935), commonly known as "the Ackermann function."
-- This is Rózsa Péter's simplified 2-argument version of Ackermann's original function.
pet :: SInteger -> SInteger -> SInteger
pet = smtFunction "pet" $ \m n ->
    ite (m .<= 0) (n + 1)
  $ ite (n .<= 0) (pet (m - 1) 1)
  $ pet (m - 1) (pet m (n - 1))

-- * Correctness

-- | Prove that @ack m 2 2 = 4@ for all m >= 0.
--
-- >>> runTP ack_2_2_4
-- Inductive lemma (strong): ack_2_2_4
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] ack_2_2_4 :: Ɐm ∷ Integer → Bool
ack_2_2_4 :: TP (Proof (Forall "m" Integer -> SBool))
ack_2_2_4 = sInduct "ack_2_2_4"
                    (\(Forall m) -> m .>= 0 .=> ack m 2 2 .== 4)
                    (\m -> m, []) $
                    \ih m -> [m .>= 0]
                          |- ack m 2 2
                          =: cases [ m .== 0 ==> trivial
                                   , m .> 0  ==> ack m 2 2
                                              =: ack (m - 1) (ack m 1 2) 2
                                              =: ack (m - 1) 2 2
                                              ?? ih `at` Inst @"m" (m - 1)
                                              =: (4 :: SInteger)
                                              =: qed
                                   ]

-- | Prove that @ack@ is non-negative when all arguments are non-negative.
-- We use strong induction on the lexicographic measure (m, n).
--
-- >>> runTP ack_psd
-- Inductive lemma (strong): ack_psd
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (4 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.4.1                         Q.E.D.
--     Step: 1.4.2                         Q.E.D.
--     Step: 1.4.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] ack_psd :: Ɐm ∷ Integer → Ɐn ∷ Integer → Ɐa ∷ Integer → Bool
ack_psd :: TP (Proof (Forall "m" Integer -> Forall "n" Integer -> Forall "a" Integer -> SBool))
ack_psd = sInduct "ack_psd"
                  (\(Forall m) (Forall n) (Forall a) ->
                      m .>= 0 .&& n .>= 0 .&& a .>= 0 .=> ack m n a .>= 0)
                  (\m n _a -> tuple (m, n), []) $
                  \ih m n a -> [m .>= 0, n .>= 0, a .>= 0]
                            |- ack m n a .>= 0
                            =: cases [ m .<= 0 ==> trivial   -- n + a >= 0
                                     , n .<= 0 ==> trivial   -- 0 >= 0
                                     , n .== 1 ==> trivial   -- a >= 0
                                     , m .> 0 .&& n .> 1
                                         ==> ack m n a .>= 0
                                          =: ack (m - 1) (ack m (n - 1) a) a .>= 0
                                          ?? ih `at` (Inst @"m" m, Inst @"n" (n - 1), Inst @"a" a)
                                          ?? ih `at` (Inst @"m" (m - 1), Inst @"n" (ack m (n - 1) a), Inst @"a" a)
                                          =: sTrue
                                          =: qed
                                     ]

-- | Prove that @pet@ is non-negative when both arguments are non-negative.
-- We use strong induction on the lexicographic measure (m, n).
--
-- >>> runTPWith cvc5 pet_psd
-- Inductive lemma (strong): pet_psd
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.3.1                         Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] pet_psd :: Ɐm ∷ Integer → Ɐn ∷ Integer → Bool
pet_psd :: TP (Proof (Forall "m" Integer -> Forall "n" Integer -> SBool))
pet_psd = do
    sInduct "pet_psd"
                  (\(Forall m) (Forall n) -> m .>= 0 .&& n .>= 0 .=> pet m n .>= 0)
                  (\m n -> tuple (m, n), []) $
                  \ih m n -> [m .>= 0, n .>= 0]
                          |- pet m n .>= 0
                          =: cases [ m .<= 0 ==> trivial   -- n + 1 >= 0
                                   , m .> 0 .&& n .<= 0
                                       ==> pet m n .>= 0
                                        =: pet (m - 1) 1 .>= 0
                                        ?? ih `at` (Inst @"m" (m - 1), Inst @"n" (1 :: SInteger))
                                        =: sTrue
                                        =: qed
                                   , m .> 0 .&& n .> 0
                                       ==> pet m n .>= 0
                                        =: pet (m - 1) (pet m (n - 1)) .>= 0
                                        ?? ih `at` (Inst @"m" m, Inst @"n" (n - 1))
                                        ?? ih `at` (Inst @"m" (m - 1), Inst @"n" (pet m (n - 1)))
                                        =: sTrue
                                        =: qed
                                   ]

-- | The main theorem: relating Ackermann and Peter functions.
--
-- We prove:
--
--   1. @pet 0 n = n + 1@
--   2. @0 < m && 0 <= n ==> pet m n + 3 = ack (m-1) (n+3) 2@
--
-- >>> runTP ackPet
-- Lemma: ackPet                           Q.E.D.
-- [Proven] ackPet :: Ɐn ∷ Integer → Bool
ackPet :: TP (Proof (Forall "n" Integer -> SBool))
ackPet = lemma "ackPet"
               (\(Forall n) -> pet 0 n .== n + 1)
               []

-- | Relating @pet@ and @ack@: @pet m n + 3 = ack (m-1) (n+3) 2@ for @m > 0@ and @n >= 0@.
--
-- >>> runTPWith cvc5 petAck
-- Inductive lemma (strong): ack_2_2_4
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): pet_psd
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.3.1                         Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): petAck
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (4 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.3.1                         Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.3.4                         Q.E.D.
--     Step: 1.3.5                         Q.E.D.
--     Step: 1.4.1                         Q.E.D.
--     Step: 1.4.2                         Q.E.D.
--     Step: 1.4.3                         Q.E.D.
--     Step: 1.4.4                         Q.E.D.
--     Step: 1.4.5                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] petAck :: Ɐm ∷ Integer → Ɐn ∷ Integer → Bool
petAck :: TP (Proof (Forall "m" Integer -> Forall "n" Integer -> SBool))
petAck = do
    ack224 <- ack_2_2_4
    psd    <- pet_psd
    sInduct "petAck"
               (\(Forall m) (Forall n) ->
                   m .> 0 .&& n .>= 0 .=> pet m n + 3 .== ack (m - 1) (n + 3) 2)
               (\m n -> tuple (m, n), []) $
               \ih m n -> [m .> 0, n .>= 0]
                       |- pet m n + 3 .== ack (m - 1) (n + 3) 2
                       =: cases [ m .== 1 .&& n .== 0
                                    ==> trivial
                                , m .== 1 .&& n .> 0
                                    ==> pet 1 n + 3 .== ack 0 (n + 3) 2
                                     =: pet 0 (pet 1 (n - 1)) + 3 .== (n + 3) + 2
                                     ?? ih `at` (Inst @"m" (1 :: SInteger), Inst @"n" (n - 1))
                                     =: sTrue
                                     =: qed
                                , m .> 1 .&& n .<= 0
                                    -- n <= 0 with n >= 0 means n == 0
                                    ==> pet m n + 3 .== ack (m - 1) (n + 3) 2
                                     -- First unfold pet: since n <= 0, pet m n = pet (m-1) 1
                                     =: pet (m - 1) 1 + 3 .== ack (m - 1) (n + 3) 2
                                     -- Unfold ack: ack (m-1) (n+3) 2 = ack (m-2) (ack (m-1) (n+2) 2) 2
                                     =: pet (m - 1) 1 + 3 .== ack (m - 2) (ack (m - 1) (n + 2) 2) 2
                                     -- Apply IH at (m-1, 1): pet (m-1) 1 + 3 = ack (m-2) 4 2
                                     ?? ih `at` (Inst @"m" (m - 1), Inst @"n" (1 :: SInteger))
                                     =: ack (m - 2) 4 2 .== ack (m - 2) (ack (m - 1) (n + 2) 2) 2
                                     -- Since n = 0, n+2 = 2, and ack (m-1) 2 2 = 4 by ack_2_2_4
                                     ?? ack224 `at` Inst @"m" (m - 1)
                                     =: sTrue
                                     =: qed
                                , m .> 1 .&& n .> 0
                                    ==> pet m n + 3 .== ack (m - 1) (n + 3) 2
                                     -- Unfold pet: pet m n = pet (m-1) (pet m (n-1))
                                     =: pet (m - 1) (pet m (n - 1)) + 3 .== ack (m - 1) (n + 3) 2
                                     -- Unfold ack on RHS: ack (m-1) (n+3) 2 = ack (m-2) (ack (m-1) (n+2) 2) 2
                                     =: pet (m - 1) (pet m (n - 1)) + 3 .== ack (m - 2) (ack (m - 1) (n + 2) 2) 2
                                     -- Use pet_psd to establish pet m (n-1) >= 0
                                     ?? psd `at` (Inst @"m" m, Inst @"n" (n - 1))
                                     -- Apply IH at (m-1, pet m (n-1)) to transform LHS
                                     ?? ih `at` (Inst @"m" (m - 1), Inst @"n" (pet m (n - 1)))
                                     =: ack (m - 2) (pet m (n - 1) + 3) 2 .== ack (m - 2) (ack (m - 1) (n + 2) 2) 2
                                     -- Apply IH at (m, n-1): pet m (n-1) + 3 = ack (m-1) (n+2) 2
                                     ?? ih `at` (Inst @"m" m, Inst @"n" (n - 1))
                                     =: sTrue
                                     =: qed
                                ]
