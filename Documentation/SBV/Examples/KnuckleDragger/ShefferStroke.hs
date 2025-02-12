-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.ShefferStroke
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Inspired by https://www.philipzucker.com/cody_sheffer/, proving
-- that the axioms of sheffer stroke (i.e., nand in traditional boolean
-- logic), imply it is a boolean algebra.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeAbstractions     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.ShefferStroke where

import Prelude hiding ((<))
import Data.List (intercalate)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- * Generalized Boolean Algebras

-- | Capture what it means to be a boolean algebra. We follow Lean's
-- definition, as much as we can: <https://leanprover-community.github.io/mathlib_docs/order/boolean_algebra.html>.
-- Since there's no way in Haskell to capture properties together with a class, we'll represent the properties
-- separately.
class BooleanAlgebra α where
  ﬧ    :: α -> α
  (⨆)  :: α -> α -> α
  (⨅)  :: α -> α -> α
  (≤)  :: α -> α -> SBool
  (<)  :: α -> α -> SBool
  (\\) :: α -> α -> α
  (⇨)  :: α -> α -> α
  ⲳ    :: α
  т    :: α

  infix  4 ≤
  infixl 6 ⨆
  infixl 7 ⨅

-- | Proofs needed for a boolean-algebra. Again, we follow Lean's definition here. Since we cannot
-- put these in the class definition above, we will keep them in a simple data-structure.
data BooleanAlgebraProof = BooleanAlgebraProof {
    le_refl          {- ∀ (a : α), a ≤ a                             -} :: Proof
  , le_trans         {- ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c         -} :: Proof
  , lt_iff_le_not_le {- (∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a)        -} :: Proof
  , le_antisymm      {- ∀ (a b : α), a ≤ b → b ≤ a → a = b           -} :: Proof
  , le_sup_left      {- ∀ (a b : α), a ≤ a ⊔ b                       -} :: Proof
  , le_sup_right     {- ∀ (a b : α), b ≤ a ⊔ b                       -} :: Proof
  , sup_le           {- ∀ (a b c : α), a ≤ c → b ≤ c → a ⊔ b ≤ c     -} :: Proof
  , inf_le_left      {- ∀ (a b : α), a ⊓ b ≤ a                       -} :: Proof
  , inf_le_right     {- ∀ (a b : α), a ⊓ b ≤ b                       -} :: Proof
  , le_inf           {- ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c     -} :: Proof
  , le_sup_inf       {- ∀ (x y z : α), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z -} :: Proof
  , inf_compl_le_bot {- ∀ (x : α), x ⊓ xᶜ ≤ ⊥                        -} :: Proof
  , top_le_sup_compl {- ∀ (x : α), ⊤ ≤ x ⊔ xᶜ                        -} :: Proof
  , le_top           {- ∀ (a : α), a ≤ ⊤                             -} :: Proof
  , bot_le           {- ∀ (a : α), ⊥ ≤ a                             -} :: Proof
  , sdiff_eq         {- (∀ (x y : α), x \ y = x ⊓ yᶜ)                -} :: Proof
  , himp_eq          {- (∀ (x y : α), x ⇨ y = y ⊔ xᶜ)                -} :: Proof
  }

-- | A somewhat prettier printer for a BooleanAlgebra proof
instance Show BooleanAlgebraProof where
  show p = intercalate "\n" [ "BooleanAlgebraProof {"
                            , "  le_refl         : " ++ show (le_refl          p)
                            , "  le_trans        : " ++ show (le_trans         p)
                            , "  lt_iff_le_not_le: " ++ show (lt_iff_le_not_le p)
                            , "  le_antisymm     : " ++ show (le_antisymm      p)
                            , "  le_sup_left     : " ++ show (le_sup_left      p)
                            , "  le_sup_right    : " ++ show (le_sup_right     p)
                            , "  sup_le          : " ++ show (sup_le           p)
                            , "  inf_le_left     : " ++ show (inf_le_left      p)
                            , "  inf_le_right    : " ++ show (inf_le_right     p)
                            , "  le_inf          : " ++ show (le_inf           p)
                            , "  le_sup_inf      : " ++ show (le_sup_inf       p)
                            , "  inf_compl_le_bot: " ++ show (inf_compl_le_bot p)
                            , "  top_le_sup_compl: " ++ show (top_le_sup_compl p)
                            , "  le_top          : " ++ show (le_top           p)
                            , "  bot_le          : " ++ show (bot_le           p)
                            , "  sdiff_eq        : " ++ show (sdiff_eq         p)
                            , "  himp_eq         : " ++ show (himp_eq          p)
                            , "}"
                            ]

-- * The sheffer stroke

-- | The abstract type for the domain.
data Stroke
mkUninterpretedSort ''Stroke

-- | The sheffer stroke operator.
(⏐) :: SStroke -> SStroke -> SStroke
(⏐) = uninterpret "⏐"
infixl 7 ⏐

-- | The boolean algebra of the sheffer stroke.
instance BooleanAlgebra SStroke where
  ﬧ x    = x ⏐ x
  a ⨆ b  = ﬧ(a ⏐ b)
  a ⨅ b  = ﬧ a ⏐ ﬧ b
  a ≤ b  = a .== b ⨅ a
  a < b  = a ≤ b .&& a ./= b
  a \\ b = a ⨅ ﬧ b
  a ⇨ b  = b ⨆ ﬧ a
  ⲳ      = arb ⏐ ﬧ arb where arb = some "ⲳ" (const sTrue)
  т      = ﬧ ⲳ

-- | Double-negation
ﬧﬧ :: BooleanAlgebra a => a -> a
ﬧﬧ = ﬧ . ﬧ

-- A couple of CPP defines make the code shorter to read
#define A      (Forall @"A"  (a  :: SStroke))
#define AAp A  (Forall @"A'" (a' :: SStroke))
#define AB  A  (Forall @"B"  (b  :: SStroke))
#define ABC AB (Forall @"C"  (c  :: SStroke))
#define X      (Forall @"X"  (x  :: SStroke))
#define XY  X  (Forall @"Y"  (y  :: SStroke))
#define XYZ XY (Forall @"Z"  (z  :: SStroke))

-- | First Sheffer axiom: @ﬧﬧa == a@
sheffer1 :: KD Proof
sheffer1 = axiom "ﬧﬧa == a" $ \A -> ﬧﬧ a .== a

-- | Second Sheffer axiom: @a ⏐ (b ⏐ ﬧb) == ﬧa@
sheffer2 :: KD Proof
sheffer2 = axiom "a ⏐ (b ⏐ ﬧb) == ﬧa" $ \AB -> a ⏐ (b ⏐ ﬧ b) .== ﬧ a

-- | Third Sheffer axiom: @ﬧ(a ⏐ (b ⏐ c)) == (ﬧb ⏐ a) ⏐ (ﬧc ⏐ a)@
sheffer3 :: KD Proof
sheffer3 = axiom "ﬧ(a ⏐ (b ⏐ c)) == (ﬧb ⏐ a) ⏐ (ﬧc ⏐ a)" $ \ABC -> ﬧ(a ⏐ (b ⏐ c)) .== (ﬧ b ⏐ a) ⏐ (ﬧ c ⏐ a)

-- * Sheffer's stroke defines a boolean algebra

-- | Prove that Sheffer stroke axioms imply it is a boolean algebra. We have:
--
-- >>> shefferBooleanAlgebra
-- Axiom: ﬧﬧa == a
-- Axiom: a ⏐ (b ⏐ ﬧb) == ﬧa
-- Axiom: ﬧ(a ⏐ (b ⏐ c)) == (ﬧb ⏐ a) ⏐ (ﬧc ⏐ a)
-- Chain lemma: a | b = b | a
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a | a′ = b | b′
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: a ⊔ b = b ⊔ a                                        Q.E.D.
-- Lemma: a ⊓ b = b ⊓ a                                        Q.E.D.
-- Lemma: a ⊔ ⲳ = a                                            Q.E.D.
-- Lemma: a ⊓ т = a                                            Q.E.D.
-- Lemma: a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)                      Q.E.D.
-- Lemma: a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)                      Q.E.D.
-- Lemma: a ⊔ aᶜ = т                                           Q.E.D.
-- Lemma: a ⊓ aᶜ = ⲳ                                           Q.E.D.
-- Chain lemma: a ⊔ т = т
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ⊓ ⲳ = ⲳ
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ⊔ (a ⊓ b) = a
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ⊓ (a ⊔ b)
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ⊓ a = a
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ⊔ a' = т → a ⊓ a' = ⲳ → a' = aᶜ
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Step  : 7                                                 Q.E.D.
--   Step  : 8                                                 Q.E.D.
--   Step  : 9                                                 Q.E.D.
--   Step  : 10                                                Q.E.D.
--   Step  : 11                                                Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: aᶜᶜ = a                                              Q.E.D.
-- Lemma: aᶜ = bᶜ → a = b                                      Q.E.D.
-- Lemma: a ⊔ bᶜ = т → a ⊓ bᶜ = ⲳ → a = b                      Q.E.D.
-- Chain lemma: a ⊔ (aᶜ ⊔ b) = т
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ⊓ (aᶜ ⊓ b) = ⲳ
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ                                   Q.E.D.
-- Lemma: (a ⨅ b)ᶜ = aᶜ ⨆ bᶜ                                   Q.E.D.
-- Lemma: (a ⊔ (b ⊔ c)) ⊔ aᶜ = т                               Q.E.D.
-- Lemma: b ⊓ (a ⊔ (b ⊔ c)) = b                                Q.E.D.
-- Lemma: b ⊔ (a ⊓ (b ⊓ c)) = b                                Q.E.D.
-- Chain lemma: (a ⊔ (b ⊔ c)) ⊔ bᶜ = т
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Step  : 7                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: (a ⊔ (b ⊔ c)) ⊔ cᶜ = т                               Q.E.D.
-- Chain lemma: (a ⊔ b ⊔ c)ᶜ ⊓ a = ⲳ
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Step  : 7                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: (a ⊔ b ⊔ c)ᶜ ⊓ b = ⲳ                                 Q.E.D.
-- Lemma: (a ⊔ b ⊔ c)ᶜ ⊓ c = ⲳ                                 Q.E.D.
-- Chain lemma: (a ⊔ (b ⊔ c)) ⊔ ((a ⊔ b) ⊔ c)ᶜ = т
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: (a ⊔ (b ⊔ c)) ⊓ ((a ⊔ b) ⊔ c)ᶜ = ⲳ
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Step  : 6                                                 Q.E.D.
--   Step  : 7                                                 Q.E.D.
--   Step  : 8                                                 Q.E.D.
--   Step  : 9                                                 Q.E.D.
--   Step  : 10                                                Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c                            Q.E.D.
-- Chain lemma: (a ⊓ (b ⊓ c))ᶜ = ((a ⊓ b) ⊓ c)ᶜ
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Step  : 5                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: a ≤ b → b ≤ a → a = b
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: a ≤ a                                                Q.E.D.
-- Chain lemma: a ≤ b → b ≤ c → a ≤ c
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Step  : 4                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: a < b ↔ a ≤ b ∧ ¬b ≤ a                               Q.E.D.
-- Lemma: a ≤ a ⊔ b                                            Q.E.D.
-- Lemma: b ≤ a ⊔ b                                            Q.E.D.
-- Chain lemma: a ≤ c → b ≤ c → a ⊔ b ≤ c
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: a ⊓ b ≤ a                                            Q.E.D.
-- Lemma: a ⊓ b ≤ b                                            Q.E.D.
-- Chain lemma: a ≤ b → a ≤ c → a ≤ b ⊓ c
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
--   Step  : 1                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: x ⊓ xᶜ ≤ ⊥                                           Q.E.D.
-- Lemma: ⊤ ≤ x ⊔ xᶜ                                           Q.E.D.
-- Chain lemma: a ≤ ⊤
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Step  : 3                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Chain lemma: ⊥ ≤ a
--   Step  : 1                                                 Q.E.D.
--   Step  : 2                                                 Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: x \ y = x ⊓ yᶜ                                       Q.E.D.
-- Lemma: x ⇨ y = y ⊔ xᶜ                                       Q.E.D.
-- BooleanAlgebraProof {
--   le_refl         : [Proven] a ≤ a
--   le_trans        : [Proven] a ≤ b → b ≤ c → a ≤ c
--   lt_iff_le_not_le: [Proven] a < b ↔ a ≤ b ∧ ¬b ≤ a
--   le_antisymm     : [Proven] a ≤ b → b ≤ a → a = b
--   le_sup_left     : [Proven] a ≤ a ⊔ b
--   le_sup_right    : [Proven] b ≤ a ⊔ b
--   sup_le          : [Proven] a ≤ c → b ≤ c → a ⊔ b ≤ c
--   inf_le_left     : [Proven] a ⊓ b ≤ a
--   inf_le_right    : [Proven] a ⊓ b ≤ b
--   le_inf          : [Proven] a ≤ b → a ≤ c → a ≤ b ⊓ c
--   le_sup_inf      : [Proven] (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
--   inf_compl_le_bot: [Proven] x ⊓ xᶜ ≤ ⊥
--   top_le_sup_compl: [Proven] ⊤ ≤ x ⊔ xᶜ
--   le_top          : [Proven] a ≤ ⊤
--   bot_le          : [Proven] ⊥ ≤ a
--   sdiff_eq        : [Proven] x \ y = x ⊓ yᶜ
--   himp_eq         : [Proven] x ⇨ y = y ⊔ xᶜ
-- }
shefferBooleanAlgebra :: IO BooleanAlgebraProof
shefferBooleanAlgebra = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

  -- Get the axioms
  sh1 <- sheffer1
  sh2 <- sheffer2
  sh3 <- sheffer3

  commut <- calcLemma "a | b = b | a" (\AB -> a ⏐ b .== b ⏐ a) $
                      \a b -> sTrue |- a ⏐ b                       ? sh1
                                    =: ﬧﬧ(a ⏐ b)                   ? sh1
                                    =: ﬧﬧ(a ⏐ ﬧﬧ b)
                                    =: ﬧﬧ(a ⏐ (ﬧ b ⏐ ﬧ b))         ? sh3
                                    =: ﬧ ((ﬧﬧ b ⏐ a) ⏐ (ﬧﬧ b ⏐ a))
                                    =: ﬧﬧ(ﬧﬧ b ⏐ a)                ? sh1
                                    =: ﬧﬧ b ⏐ a                    ? sh1
                                    =: b ⏐ a
                                    =: qed

  all_bot <- calcLemma "a | a′ = b | b′" (\AB -> a ⏐ ﬧ a .== b ⏐ ﬧ b) $
                       \a b -> sTrue |- a ⏐ ﬧ a                  ? sh1
                                     =: ﬧﬧ(a ⏐ ﬧ a)              ? sh2
                                     =: ﬧ((a ⏐ ﬧ a) ⏐ (b ⏐ ﬧ b)) ? commut
                                     =: ﬧ((b ⏐ ﬧ b) ⏐ (a ⏐ ﬧ a)) ? sh2
                                     =: ﬧﬧ (b ⏐ ﬧ b)             ? sh1
                                     =: b ⏐ ﬧ b
                                     =: qed

  commut1  <- lemma "a ⊔ b = b ⊔ a" (\AB -> a ⨆ b .== b ⨆ a) [commut]
  commut2  <- lemma "a ⊓ b = b ⊓ a" (\AB -> a ⨅ b .== b ⨅ a) [commut]

  ident1   <- lemma "a ⊔ ⲳ = a" (\A  -> a ⨆ ⲳ .== a) [sh1, sh2]
  ident2   <- lemma "a ⊓ т = a" (\A  -> a ⨅ т .== a) [sh1, sh2]

  distrib1 <- lemma "a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)" (\ABC -> a ⨆ (b ⨅ c) .== (a ⨆ b) ⨅ (a ⨆ c)) [sh1, sh3, commut]
  distrib2 <- lemma "a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)" (\ABC -> a ⨅ (b ⨆ c) .== (a ⨅ b) ⨆ (a ⨅ c)) [sh1, sh3, commut]

  compl1 <- lemma "a ⊔ aᶜ = т" (\A -> a ⨆ ﬧ a .== т) [sh1, sh2, sh3, all_bot]
  compl2 <- lemma "a ⊓ aᶜ = ⲳ" (\A -> a ⨅ ﬧ a .== ⲳ) [sh1, commut, all_bot]

  bound1 <- calcLemma "a ⊔ т = т" (\A -> a ⨆ т .== т) $
                      \(a :: SStroke) -> sTrue |- a ⨆ т               ? ident2
                                               =: (a ⨆ т) ⨅ т         ? commut2
                                               =: т ⨅ (a ⨆ т)         ? compl1
                                               =: (a ⨆ ﬧ a) ⨅ (a ⨆ т) ? distrib1
                                               =: a ⨆ (ﬧ a ⨅ т)       ? ident2
                                               =: a ⨆ ﬧ a             ? compl1
                                               =: (т :: SStroke)
                                               =: qed

  bound2 <- calcLemma "a ⊓ ⲳ = ⲳ" (\A -> a ⨅ ⲳ .== ⲳ) $
                      \(a :: SStroke) -> sTrue |- a ⨅ ⲳ               ? ident1
                                               =: (a ⨅ ⲳ) ⨆ ⲳ         ? commut1
                                               =: ⲳ ⨆ (a ⨅ ⲳ)         ? compl2
                                               =: (a ⨅ ﬧ a) ⨆ (a ⨅ ⲳ) ? distrib2
                                               =: a ⨅ (ﬧ a ⨆ ⲳ)       ? ident1
                                               =: a ⨅ ﬧ a             ? compl2
                                               =: (ⲳ :: SStroke)
                                               =: qed

  absorb1 <- calcLemma "a ⊔ (a ⊓ b) = a" (\AB -> a ⨆ (a ⨅ b) .== a) $
                       \(a :: SStroke) b -> sTrue |- a ⨆ (a ⨅ b)       ? ident2
                                                  =: (a ⨅ т) ⨆ (a ⨅ b) ? distrib2
                                                  =: a ⨅ (т ⨆ b)       ? commut1
                                                  =: a ⨅ (b ⨆ т)       ? bound1
                                                  =: a ⨅ т             ? ident2
                                                  =: a
                                                  =: qed

  absorb2 <- calcLemma "a ⊓ (a ⊔ b) = a" (\AB -> a ⨅ (a ⨆ b) .== a) $
                       \(a :: SStroke) b -> sTrue |- a ⨅ (a ⨆ b)       ? ident1
                                                  =: (a ⨆ ⲳ) ⨅ (a ⨆ b) ? distrib1
                                                  =: a ⨆ (ⲳ ⨅ b)       ? commut2
                                                  =: a ⨆ (b ⨅ ⲳ)       ? bound2
                                                  =: a ⨆ ⲳ             ? ident1
                                                  =: a
                                                  =: qed

  idemp2 <- calcLemma "a ⊓ a = a" (\A -> a ⨅ a .== a) $
                      \(a :: SStroke) -> sTrue |- a ⨅ a       ? ident1
                                               =: a ⨅ (a ⨆ ⲳ) ? absorb2 
                                               =: a
                                               =: qed

  inv <- calcLemma "a ⊔ a' = т → a ⊓ a' = ⲳ → a' = aᶜ"
                   (\AAp  -> a ⨆ a' .== т .=> a ⨅ a' .== ⲳ .=> a' .== ﬧ a) $
                   \(a :: SStroke) a' -> a ⨆ a' .== т .&& a ⨅ a' .== ⲳ |- a'                     ? ident2
                                                                       =: a' ⨅ т                 ? compl1
                                                                       =: a' ⨅ (a ⨆ ﬧ a)         ? distrib2
                                                                       =: (a' ⨅ a) ⨆ (a' ⨅ ﬧ a)  ? commut2
                                                                       =: (a' ⨅ a) ⨆ (ﬧ a ⨅ a')  ? commut2
                                                                       =: (a ⨅ a') ⨆ (ﬧ a ⨅ a')  ? compl2
                                                                       =: ⲳ ⨆ (ﬧ a ⨅ a')         ? compl2
                                                                       =: (a ⨅ ﬧ a) ⨆ (ﬧ a ⨅ a') ? commut2
                                                                       =: (ﬧ a ⨅ a) ⨆ (ﬧ a ⨅ a') ? distrib2
                                                                       =: ﬧ a ⨅ (a ⨆ a')
                                                                       =: ﬧ a ⨅ т                ? ident2
                                                                       =: ﬧ a
                                                                       =: qed

  dne      <- lemma "aᶜᶜ = a"         (\A -> ﬧﬧ a .== a)               [inv, compl1, compl2, commut1, commut2]
  inv_elim <- lemma "aᶜ = bᶜ → a = b" (\AB -> ﬧ a .== ﬧ b .=> a .== b) [dne]

  cancel <- lemma "a ⊔ bᶜ = т → a ⊓ bᶜ = ⲳ → a = b" (\AB -> a ⨆ ﬧ b .== т .=> a ⨅ ﬧ b .== ⲳ .=> a .== b) [inv, inv_elim]

  a1 <- calcLemma "a ⊔ (aᶜ ⊔ b) = т" (\AB  -> a ⨆ (ﬧ a ⨆ b) .== т) $
                  \(a :: SStroke) b -> sTrue |- a ⨆ (ﬧ a ⨆ b)               ? ident2
                                             =: (a ⨆ (ﬧ a ⨆ b)) ⨅ т         ? commut2
                                             =: т ⨅ (a ⨆ (ﬧ a ⨆ b))         ? compl1
                                             =: (a ⨆ ﬧ a) ⨅ (a ⨆ (ﬧ a ⨆ b)) ? distrib1
                                             =: a ⨆ (ﬧ a ⨅ (ﬧ a ⨆ b))       ? absorb2
                                             =: a ⨆ ﬧ a                     ? compl1
                                             =: (т :: SStroke)
                                             =: qed

  a2 <- calcLemma "a ⊓ (aᶜ ⊓ b) = ⲳ" (\AB  -> a ⨅ (ﬧ a ⨅ b) .== ⲳ) $
                  \(a :: SStroke) b -> sTrue |- a ⨅ (ﬧ a ⨅ b)               ? ident1
                                             =: (a ⨅ (ﬧ a ⨅ b)) ⨆ ⲳ         ? commut1
                                             =: ⲳ ⨆ (a ⨅ (ﬧ a ⨅ b))         ? compl2
                                             =: (a ⨅ ﬧ a) ⨆ (a ⨅ (ﬧ a ⨅ b)) ? distrib2
                                             =: a ⨅ (ﬧ a ⨆ (ﬧ a ⨅ b))       ? absorb1
                                             =: a ⨅ ﬧ a                     ? compl2
                                             =: (ⲳ :: SStroke)
                                             =: qed

  dm1 <- lemma "(a ⊔ b)ᶜ = aᶜ ⊓ bᶜ" (\AB -> ﬧ(a ⨆ b) .== ﬧ a ⨅ ﬧ b)
               [a1, a2, dne, commut1, commut2, ident1, ident2, distrib1, distrib2]

  dm2 <- lemma "(a ⨅ b)ᶜ = aᶜ ⨆ bᶜ" (\AB -> ﬧ(a ⨅ b) .== ﬧ a ⨆ ﬧ b)
               [a1, a2, dne, commut1, commut2, ident1, ident2, distrib1, distrib2]


  d1 <- lemma "(a ⊔ (b ⊔ c)) ⊔ aᶜ = т" (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ a .== т)
              [a1, a2, commut1, ident1, ident2, distrib1, compl1, compl2, dm1, dm2, idemp2]

  e1 <- lemma "b ⊓ (a ⊔ (b ⊔ c)) = b" (\ABC -> b ⨅ (a ⨆ (b ⨆ c)) .== b) [distrib2, absorb1, absorb2, commut1]

  e2 <- lemma "b ⊔ (a ⊓ (b ⊓ c)) = b" (\ABC -> b ⨆ (a ⨅ (b ⨅ c)) .== b) [distrib1, absorb1, absorb2, commut2]

  f1 <- calcLemma "(a ⊔ (b ⊔ c)) ⊔ bᶜ = т" (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ b .== т) $
                  \(a :: SStroke) b c -> sTrue |- (a ⨆ (b ⨆ c)) ⨆ ﬧ b               ? commut1
                                               =: ﬧ b ⨆ (a ⨆ (b ⨆ c))               ? ident2
                                               =: (ﬧ b ⨆ (a ⨆ (b ⨆ c))) ⨅ т         ? commut2
                                               =: т ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c)))         ? compl1
                                               =: (b ⨆ ﬧ b) ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c))) ? commut1
                                               =: (ﬧ b ⨆ b) ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c))) ? distrib1
                                               =: ﬧ b ⨆ (b ⨅ (a ⨆ (b ⨆ c)))         ? e1
                                               =: ﬧ b ⨆ b                           ? commut1
                                               =: b ⨆ ﬧ b                           ? compl1
                                               =: (т :: SStroke)
                                               =: qed

  g1 <- lemma "(a ⊔ (b ⊔ c)) ⊔ cᶜ = т" (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ c .== т) [commut1, f1]

  h1 <- calcLemma "(a ⊔ b ⊔ c)ᶜ ⊓ a = ⲳ" (\ABC -> ﬧ(a ⨆ b ⨆ c) ⨅ a .== ⲳ) $
                  \(a :: SStroke) b c -> sTrue |- ﬧ(a ⨆ b ⨆ c) ⨅ a                    ? commut2
                                               =: a ⨅ ﬧ (a ⨆ b ⨆ c)                   ? dm1
                                               =: a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)               ? ident1
                                               =: (a ⨅  (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)) ⨆ ⲳ        ? commut1
                                               =: ⲳ ⨆ (a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))         ? compl2
                                               =: (a ⨅ ﬧ a) ⨆ (a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)) ? distrib2
                                               =: a ⨅ (ﬧ a ⨆ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))       ? commut2
                                               =: a ⨅ (ﬧ a ⨆ (ﬧ c ⨅ (ﬧ a ⨅ ﬧ b)))     ? e2
                                               =: a ⨅ ﬧ a                             ? compl2
                                               =: (ⲳ :: SStroke)
                                               =: qed

  i1 <- lemma "(a ⊔ b ⊔ c)ᶜ ⊓ b = ⲳ" (\ABC -> ﬧ(a ⨆ b ⨆ c) ⨅ b .== ⲳ) [commut1, h1]
  j1 <- lemma "(a ⊔ b ⊔ c)ᶜ ⊓ c = ⲳ" (\ABC -> ﬧ(a ⨆ b ⨆ c) ⨅ c .== ⲳ) [a2, dne, commut2]

  assoc1 <- do
    c1 <- calcLemma "(a ⊔ (b ⊔ c)) ⊔ ((a ⊔ b) ⊔ c)ᶜ = т"
                    (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ((a ⨆ b) ⨆ c) .== т) $
                    \(a :: SStroke) b c -> sTrue |- (a ⨆ (b ⨆ c)) ⨆ ﬧ((a ⨆ b) ⨆ c)                        ? dm1
                                                 =: (a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)                     ? distrib1
                                                 =: ((a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b)) ⨅ ((a ⨆ (b ⨆ c)) ⨆ ﬧ c) ? g1
                                                 =: ((a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b)) ⨅ т                     ? ident2
                                                 =: (a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b)                           ? distrib1
                                                 =: ((a ⨆ (b ⨆ c)) ⨆ ﬧ a) ⨅ ((a ⨆ (b ⨆ c)) ⨆ ﬧ b)         ? d1
                                                 =: т ⨅ ((a ⨆ (b ⨆ c)) ⨆ ﬧ b)                             ? f1
                                                 =: т ⨅ (т :: SStroke)                                    ? idemp2
                                                 =: (т :: SStroke)
                                                 =: qed

    c2 <- calcLemma "(a ⊔ (b ⊔ c)) ⊓ ((a ⊔ b) ⊔ c)ᶜ = ⲳ"
                    (\ABC -> (a ⨆ (b ⨆ c)) ⨅ ﬧ((a ⨆ b) ⨆ c) .== ⲳ) $
                    \(a :: SStroke) b c -> sTrue |- (a ⨆ (b ⨆ c)) ⨅ ﬧ((a ⨆ b) ⨆ c)                    ? commut2
                                                 =: ﬧ((a ⨆ b) ⨆ c) ⨅ (a ⨆ (b ⨆ c))                    ? distrib2
                                                 =: (ﬧ((a ⨆ b) ⨆ c) ⨅ a) ⨆ (ﬧ((a ⨆ b) ⨆ c) ⨅ (b ⨆ c)) ? commut2
                                                 =: (a ⨅ ﬧ((a ⨆ b) ⨆ c)) ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)) ? commut2
                                                 =: (ﬧ((a ⨆ b) ⨆ c) ⨅ a) ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)) ? h1
                                                 =: ⲳ ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c))                    ? commut1
                                                 =: ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)) ⨆ ⲳ                    ? ident1
                                                 =: (b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)                          ? commut2
                                                 =: ﬧ((a ⨆ b) ⨆ c) ⨅ (b ⨆ c)                          ? distrib2
                                                 =: (ﬧ((a ⨆ b) ⨆ c) ⨅ b) ⨆ (ﬧ((a ⨆ b) ⨆ c) ⨅ c)       ? j1
                                                 =: (ﬧ((a ⨆ b) ⨆ c) ⨅ b) ⨆ ⲳ                          ? i1
                                                 =: ⲳ ⨆ (ⲳ :: SStroke)                                ? ident1
                                                 =: (ⲳ :: SStroke)
                                                 =: qed

    lemma "a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c" (\ABC -> a ⨆ (b ⨆ c) .== (a ⨆ b) ⨆ c) [c1, c2, cancel]

  assoc2 <- calcLemma "a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c" (\ABC -> a ⨅ (b ⨅ c) .== (a ⨅ b) ⨅ c) $
                      \(a :: SStroke) b c -> sTrue |- a ⨅ (b ⨅ c)     ? dne
                                                   =: ﬧﬧ(a ⨅ (b ⨅ c)) ? assoc1
                                                   =: ﬧﬧ((a ⨅ b) ⨅ c) ? dne
                                                   =:   ((a ⨅ b) ⨅ c)
                                                   =: qed

  le_antisymm <- calcLemma "a ≤ b → b ≤ a → a = b" (\AB -> a ≤ b .=> b ≤ a .=> a .== b) $
                           \(a :: SStroke) b -> a ≤ b .&& b ≤ a |- a
                                                                =: b ⨅ a ? commut2
                                                                =: a ⨅ b
                                                                =: b
                                                                =: qed

  le_refl <- lemma "a ≤ a" (\A -> a ≤ a) [idemp2]

  le_trans <- calcLemma "a ≤ b → b ≤ c → a ≤ c" (\ABC -> a ≤ b .=> b ≤ c .=> a ≤ c) $
                        \(a :: SStroke) b c -> a ≤ b .&& b ≤ c |- a
                                                               =: b ⨅ a
                                                               =: (c ⨅ b) ⨅ a  ? assoc2
                                                               =: c ⨅ (b ⨅ a)
                                                               =: (c ⨅ a)
                                                               =: qed

  lt_iff_le_not_le <- lemma "a < b ↔ a ≤ b ∧ ¬b ≤ a" (\AB -> (a < b) .<=> a ≤ b .&& sNot (b ≤ a)) [sh3]

  le_sup_left  <- lemma "a ≤ a ⊔ b" (\AB -> a ≤ a ⨆ b) [commut1, commut2, absorb2]
  le_sup_right <- lemma "b ≤ a ⊔ b" (\AB -> a ≤ a ⨆ b) [commut1, commut2, absorb2]

  sup_le <- calcLemma "a ≤ c → b ≤ c → a ⊔ b ≤ c"
                      (\ABC -> a ≤ c .=> b ≤ c .=> a ⨆ b ≤ c) $
                      \(a :: SStroke) b c -> a ≤ c .&& b ≤ c |- a ⨆ b
                                                             =: (c ⨅ a) ⨆ (c ⨅ b) ? distrib2
                                                             =: c ⨅ (a ⨆ b)
                                                             =: qed

  inf_le_left  <- lemma "a ⊓ b ≤ a" (\AB -> a ⨅ b ≤ a) [assoc2, idemp2]
  inf_le_right <- lemma "a ⊓ b ≤ b" (\AB -> a ⨅ b ≤ b) [commut2, inf_le_left]

  le_inf <- calcLemma "a ≤ b → a ≤ c → a ≤ b ⊓ c"
                      (\ABC -> a ≤ b .=> a ≤ c .=> a ≤ b ⨅ c) $
                      \(a :: SStroke) b c -> a ≤ b .&& a ≤ c |- a
                                                             =: b ⨅ a
                                                             =: b ⨅ (c ⨅ a) ? assoc2
                                                             =: (b ⨅ c ⨅ a)
                                                             =: qed

  le_sup_inf <- lemma "(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z"
                      (\XYZ -> (x ⨆ y) ⨅ (x ⨆ z) ≤ x ⨆ y ⨅ z)
                      [distrib1, le_refl]

  inf_compl_le_bot <- lemma "x ⊓ xᶜ ≤ ⊥" (\X -> x ⨅ ﬧ x ≤ ⲳ) [compl2, le_refl]
  top_le_sup_compl <- lemma "⊤ ≤ x ⊔ xᶜ" (\X -> т ≤ x ⨆ ﬧ x) [compl1, le_refl]

  le_top <- calcLemma "a ≤ ⊤" (\A -> a ≤ т) $
                      \(a :: SStroke)-> sTrue |- a ≤ т
                                              =: a .== т ⨅ a ? commut2
                                              =: a .== a ⨅ т ? ident2
                                              =: a .== a
                                              =: qed

  bot_le <- calcLemma "⊥ ≤ a" (\A -> ⲳ ≤ a) $
                      \(a :: SStroke) -> sTrue |- ⲳ ≤ a 
                                               =: ⲳ .== a ⨅ ⲳ           ? bound2
                                               =: (ⲳ .== (ⲳ :: SStroke))
                                               =: qed

  sdiff_eq <- lemma "x \\ y = x ⊓ yᶜ" (\XY -> x \\ y .== x ⨅ ﬧ y) []
  himp_eq  <- lemma "x ⇨ y = y ⊔ xᶜ"  (\XY -> x ⇨ y .== y ⨆ ﬧ x)  []

  pure BooleanAlgebraProof {
            le_refl          {- ∀ (a : α), a ≤ a                             -} = le_refl
          , le_trans         {- ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c         -} = le_trans
          , lt_iff_le_not_le {- (∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a)        -} = lt_iff_le_not_le
          , le_antisymm      {- ∀ (a b : α), a ≤ b → b ≤ a → a = b           -} = le_antisymm
          , le_sup_left      {- ∀ (a b : α), a ≤ a ⊔ b                       -} = le_sup_left
          , le_sup_right     {- ∀ (a b : α), b ≤ a ⊔ b                       -} = le_sup_right
          , sup_le           {- ∀ (a b c : α), a ≤ c → b ≤ c → a ⊔ b ≤ c     -} = sup_le
          , inf_le_left      {- ∀ (a b : α), a ⊓ b ≤ a                       -} = inf_le_left
          , inf_le_right     {- ∀ (a b : α), a ⊓ b ≤ b                       -} = inf_le_right
          , le_inf           {- ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c     -} = le_inf
          , le_sup_inf       {- ∀ (x y z : α), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z -} = le_sup_inf
          , inf_compl_le_bot {- ∀ (x : α), x ⊓ xᶜ ≤ ⊥                        -} = inf_compl_le_bot
          , top_le_sup_compl {- ∀ (x : α), ⊤ ≤ x ⊔ xᶜ                        -} = top_le_sup_compl
          , le_top           {- ∀ (a : α), a ≤ ⊤                             -} = le_top
          , bot_le           {- ∀ (a : α), ⊥ ≤ a                             -} = bot_le
          , sdiff_eq         {- (∀ (x y : α), x \ y = x ⊓ yᶜ)                -} = sdiff_eq
          , himp_eq          {- (∀ (x y : α), x ⇨ y = y ⊔ xᶜ)                -} = himp_eq
       }
