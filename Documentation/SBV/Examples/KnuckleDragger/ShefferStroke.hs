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

{-# LANGUAGE CPP                #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeAbstractions   #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.ShefferStroke where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- * The sheffer stroke

-- | The abstract type for the domain.
data Stroke
mkUninterpretedSort ''Stroke

-- | The sheffer stroke operator
(⏐) :: SStroke -> SStroke -> SStroke
(⏐) = uninterpret "⏐"
infixl 7 ⏐

-- | Negation in terms of ⏐
ﬧ :: SStroke -> SStroke
ﬧ x = x ⏐ x

-- | First Sheffer axiom @ﬧﬧa == a@
sheffer1 :: KD Proof
sheffer1 = axiom "ﬧﬧa == a" $ \(Forall @"a" a) -> ﬧ (ﬧ a) .== a

-- | Second Sheffer axiom @a ⏐ (b ⏐ ﬧb) == ﬧa@
sheffer2 :: KD Proof
sheffer2 = axiom "a ⏐ (b ⏐ ﬧb) == ﬧa" $ \(Forall @"a" a) (Forall @"b" b) -> a ⏐ (b ⏐ ﬧ b) .== ﬧ a

-- | Third Sheffer axiom @ﬧ(a ⏐ (b ⏐ c)) == (ﬧb ⏐ a) ⏐ (ﬧc ⏐ a)@
sheffer3 :: KD Proof
sheffer3 = axiom "ﬧ(a ⏐ (b ⏐ c)) == (ﬧb ⏐ a) ⏐ (ﬧc ⏐ a)"
               $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> ﬧ (a ⏐ (b ⏐ c)) .== (ﬧ b ⏐ a) ⏐ (ﬧ c ⏐ a)

-- * Infimum, supremum, bottom, and top

-- | Infimum: Greatest lower bound.
(⨅) :: SStroke -> SStroke -> SStroke
a ⨅ b = ﬧ a ⏐ ﬧ b

-- | Supremum: Least upper bound.
(⨆) :: SStroke -> SStroke -> SStroke
a ⨆ b = ﬧ (a ⏐ b)

-- | The unique bottom element
z :: SStroke
z = elt ⏐ ﬧ elt
 where elt = uninterpret "z_witness"

-- | The unique top element
u :: SStroke
u = ﬧ z

-- * Sheffer's stroke defines a boolean algebra

-- | Prove that Sheffer stroke axioms imply it is a boolean algebra. We have:
--
-- TODO: Due to doctest issues, the output here does not get tested.
-- See: https://github.com/yav/haskell-lexer/issues/14, which seems to be the root cause.
-- >>> shefferBooleanAlgebra
shefferBooleanAlgebra :: IO Proof
shefferBooleanAlgebra = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

  sh1 <- sheffer1
  sh2 <- sheffer2
  sh3 <- sheffer3

  commut <- chainLemma "a ⏐ b == b ⏐ a"
                       (\(Forall @"a" a) (Forall @"b" b) -> a ⏐ b .== b ⏐ a)
                       (\a b -> (sTrue, [ a ⏐ b
                                        , ﬧ (ﬧ (a ⏐ b))
                                        , ﬧ (ﬧ (a ⏐ ﬧ (ﬧ b)))
                                        , ﬧ (ﬧ (ﬧ (ﬧ b) ⏐ a))
                                        , b ⏐ a
                                        ]))
                       [sh1, sh3]

  all_bot <- chainLemma "a ⏐ ﬧa == b ⏐ ﬧb"
                        (\(Forall @"a" a) (Forall @"b" b) -> a ⏐ ﬧ a .== b ⏐ ﬧ b)
                        (\a b -> (sTrue, [ a ⏐ ﬧ a
                                         , ﬧ ((a ⏐ ﬧ a) ⏐ (b ⏐ ﬧ b))
                                         , ﬧ ((b ⏐ ﬧ b) ⏐ (a ⏐ ﬧ a))
                                         , ﬧ (ﬧ (b ⏐ ﬧ b))
                                         , b ⏐ ﬧ b
                                         ]))
                        [sh1, sh2, commut]

  commut1 <- lemma "a ⊔ b == b ⊔ a"
                   (\(Forall @"a" a) (Forall @"b" b) -> a ⨆ b .== b ⨆ a)
                   [commut]

  commut2 <- lemma "a ⊓ b == b ⊓ a"
                   (\(Forall @"a" a) (Forall @"b" b) -> a ⨅ b .== b ⨅ a)
                   [commut]

  ident1 <- lemma "a ⊔ z == a"
                  (\(Forall @"a" a) -> a ⨆ z .== a)
                  [sh1, sh2]

  ident2 <- lemma "a ⊓ u == a"
                  (\(Forall @"a" a) -> a ⨅ u .== a)
                  [sh1, sh2]

  distrib1 <- lemma "a ⊔ (b ⊓ c) == (a ⊔ b) ⊓ (a ⊔ c)"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a ⨆ (b ⨅ c) .== (a ⨆ b) ⨅ (a ⨆ c))
                    [sh1, sh3, commut]

  distrib2 <- lemma "a ⊓ (b ⊔ c) == (a ⊓ b) ⊔ (a ⊓ c)"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a ⨅ (b ⨆ c) .== (a ⨅ b) ⨆ (a ⨅ c))
                    [sh1, sh3, commut]

  compl1 <- lemma "a ⊔ ﬧa == u"
                  (\(Forall @"a" a) -> a ⨆ ﬧ a .== u)
                  [sh1, sh2, sh3, all_bot]

  compl2 <- lemma "a ⊓ ﬧa == z"
                  (\(Forall @"a" a) -> a ⨅ ﬧ a .== z)
                  [sh1, sh2, sh3]

  bound1 <- chainLemma "a ⊔ u == u"
                       (\(Forall @"a" a) -> a ⨆ u .== u)
                       (\a -> (sTrue, [ a ⨆ u
                                      , (a ⨆ u) ⨅ u
                                      , u ⨅ (a ⨆ u)
                                      , (a ⨆ ﬧ a) ⨅ (a ⨆ u)
                                      , a ⨆ (ﬧ a ⨅ u)
                                      , a ⨆ ﬧ a
                                      , u
                                      ]))
                       [ident2, commut2, compl1, distrib1]

  bound2 <- chainLemma "a ⊓ z == z"
                       (\(Forall @"a" a) -> a ⨅ z .== z)
                       (\a -> (sTrue, [ a ⨅ z
                                      , (a ⨅ z) ⨆ z
                                      , z ⨆ (a ⨅ z)
                                      , (a ⨅ ﬧ a) ⨆ (a ⨅ z)
                                      , a ⨅ (ﬧ a ⨆ z)
                                      , a ⨅ ﬧ a
                                      , z
                                      ]))
                       [ident1, commut1, compl2, distrib2, ident1, compl2]

  -- TODO: absorb1
  _bsorb1 <- chainLemma "a ⊔ (a ⊓ b) == a"
                        (\(Forall @"a" a) (Forall @"b" b) -> a ⨆ (a ⨅ b) .== a)
                        (\a b -> (sTrue, [ a ⨆ (a ⨅ b)
                                         , (a ⨅ u) ⨆ (a ⨅ b)
                                         , a ⨅ (u ⨆ b)
                                         , a ⨅ (b ⨆ u)
                                         , a ⨅ u
                                         , a
                                         ]))
                        [ident2, distrib2, commut1, bound1]

  absorb2 <- chainLemma "a ⊓ (a ⊔ b) == a"
                        (\(Forall @"a" a) (Forall @"b" b) -> a ⨅ (a ⨆ b) .== a)
                        (\a b -> (sTrue, [ a ⨅ (a ⨆ b)
                                         , (a ⨆ z) ⨅ (a ⨆ b)
                                         , a ⨆ (z ⨅ b)
                                         , a ⨆ (b ⨅ z)
                                         , a ⨆ z
                                         , a
                                         ]))
                        [ident1, distrib1, commut2, bound2]

  -- TODO: idemp2
  _demp2 <- chainLemma "a ⊓ a == a"
                       (\(Forall @"a" a) -> a ⨅ a .== a)
                       (\a -> (sTrue, [ a ⨅ a
                                      , a ⨅ (a ⨆ z)
                                      , a
                                      ]))
                       [ident1, absorb2]

  inv <- chainLemma "a ⨆ a' == u → a ⨅ a' == z → a' = ﬧ a"
                    (\(Forall @"a" a) (Forall @"a'" a') -> a ⨆ a' .== u .=> a ⨅ a' .== z .=> a' .== ﬧ a)
                    (\a a' -> (a ⨆ a' .== u .&& a ⨅ a' .== z, [ a'
                                                              , a' ⨅ u
                                                              , a' ⨅ (a ⨆ ﬧ a)
                                                              , (a' ⨅ a) ⨆ (a' ⨅ ﬧ a)
                                                              , (a' ⨅ a) ⨆ (ﬧ a ⨅ a')
                                                              , (a ⨅ a') ⨆ (ﬧ a ⨅ a')
                                                              , z ⨆ (ﬧ a ⨅ a')
                                                              , (a ⨅ ﬧ a) ⨆ (ﬧ a ⨅ a')
                                                              , (ﬧ a ⨅ a) ⨆ (ﬧ a ⨅ a')
                                                              , ﬧ a ⨅ (a ⨆ a')
                                                              , ﬧ a ⨅ u
                                                              , ﬧ a
                                                              ]))
                    [ident2, compl1, distrib2, commut2]

  dne <- lemma "ﬧ (ﬧ a) == a"
               (\(Forall @"a" a) -> ﬧ (ﬧ a) .== a)
               [inv, compl1, compl2, commut1, commut2]

  -- TODO: inv_elim
  _nv_elim <- lemma "ﬧ a == ﬧ b → a == b"
                    (\(Forall @"a" a) (Forall @"b" b) -> ﬧ a .== ﬧ b .=> a .== b)
                    [dne]

  pure sorry

{-
lemma cancel (a b : α) : a ⊔ bᶜ = u → a ⊓ bᶜ = z → a = b := by
  intro h₁ h₂
  have h : bᶜ = aᶜ := by apply inv <;> trivial
  apply inv_elim; symm; trivial

@[simp]
lemma A₁ (a b : α) : a ⊔ (aᶜ ⊔ b) = u := by
  calc
    a ⊔ (aᶜ ⊔ b) = (a ⊔ (aᶜ ⊔ b)) ⊓ u := by rw [ident₂]
    _            = u ⊓ (a ⊔ (aᶜ ⊔ b)) := by rw [commut₂]
    _            = (a ⊔ aᶜ) ⊓ (a ⊔ (aᶜ ⊔ b)) := by rw [compl₁]
    _            = a ⊔ (aᶜ ⊓ (aᶜ ⊔ b)) := by rw [distrib₁]
    _            = a ⊔ aᶜ := by rw [absorb₂, compl₁]
    _            = u := by rw [compl₁]

@[simp]
lemma A₂ (a b : α) : a ⊓ (aᶜ ⊓ b) = z := by
  calc
    a ⊓ (aᶜ ⊓ b) = (a ⊓ (aᶜ ⊓ b)) ⊔ z := by rw [ident₁]
    _            = z ⊔ (a ⊓ (aᶜ ⊓ b)) := by rw [commut₁]
    _            = (a ⊓ aᶜ) ⊔ (a ⊓ (aᶜ ⊓ b)) := by rw [compl₂]
    _            = a ⊓ (aᶜ ⊔ (aᶜ ⊓ b)) := by rw [distrib₂]
    _            = a ⊓ aᶜ := by rw [absorb₁, compl₂]
    _            = z := by rw [compl₂]


@[simp]
lemma dm₁ (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₁, distrib₁]
    conv => left; left; rw [commut₁]; right; left; exact Eq.symm (dne a)
    rw [A₁, commut₂, ident₂, commut₁]
    conv => left; right; rw [commut₁]; left; exact Eq.symm (dne b)
    simp
  . rw [distrib₂]
    conv => left; left; rw [commut₂]
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]
    simp

@[simp]
lemma dm₂ (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₂, distrib₁]
    conv => left; left; rw [commut₁]; right; rw [commut₁]
    rw [A₁, commut₂, ident₂]
    rw [commut₁]
    rw [A₁]
  . rw [commut₂, distrib₂]
    conv => left; left; rw [commut₂]; right; left; exact Eq.symm (dne a)
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]; left; exact Eq.symm (dne b)
    rw [A₂]

lemma D₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ aᶜ = u := by
  rw [commut₁]
  conv => left; right; left; exact Eq.symm (dne a)
  simp

lemma E₁ (a b c : α) : b ⊓ (a ⊔ (b ⊔ c)) = b := by rw [distrib₂, absorb₂, commut₁, absorb₁]

lemma E₂ (a b c : α) : b ⊔ (a ⊓ (b ⊓ c)) = b := by rw [distrib₁, absorb₁, commut₂, absorb₂]

lemma F₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ bᶜ = u := by
  calc
    (a ⊔ (b ⊔ c)) ⊔ bᶜ = bᶜ ⊔ (a ⊔ (b ⊔ c)) := by rw [commut₁]
    _                  = u ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by rw [commut₂]; simp
    _                  = (b ⊔ bᶜ) ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by simp
    _                  = (bᶜ ⊔ b) ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by rw [commut₁]
    _                  = bᶜ ⊔ (b ⊓ (a ⊔ (b ⊔ c))) := by rw [distrib₁]
    _                  = bᶜ ⊔ b := by rw [E₁]
    _                  = u := by rw [commut₁]; simp

lemma G₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ cᶜ = u := by
  conv => left; left; right; rw [commut₁]
  apply F₁

lemma H₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ a = z := by
  simp; rw [commut₂]
  calc
    a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ) = (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) ⊔ z := by rw [ident₁]
    _                  = z ⊔ (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [commut₁]
    _                  = (a ⊓ aᶜ) ⊔ (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [compl₂]
    _                  = a ⊓ (aᶜ ⊔ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [distrib₂]
    _                  = a ⊓ (aᶜ ⊔ (cᶜ ⊓ (aᶜ ⊓ bᶜ))) := by conv => left; right; right; rw [commut₂]
    _                  = a ⊓ aᶜ := by rw [E₂]
    _                  = z := by rw [compl₂]

lemma I₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ b = z := by
  conv => left; left; arg 1; left; rw [commut₁]
  exact H₁ ..

lemma J₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ c = z := by
  simp
  rw [commut₂]
  conv => left; right; rw [commut₂]
  simp

-- Incredibly, these are derivable
@[simp]
lemma assoc₁ (a b c : α) : a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c := by
  apply cancel; simp
  . calc
      (a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ ⊓ cᶜ) = ((a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ)) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) := by rw [distrib₁]
      _ = ((a ⊔ (b ⊔ c) ⊔ aᶜ) ⊓ ((a ⊔ (b ⊔ c) ⊔ bᶜ))) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) := by rw [distrib₁]
      _ = (u ⊓ u) ⊓ u := by rw [D₁, F₁, G₁]
      _ = u := by simp
  . rw [commut₂]
    rw [distrib₂]; rw [distrib₂]
    calc
      (a ⊔ b ⊔ c)ᶜ ⊓ a ⊔ ((a ⊔ b ⊔ c)ᶜ ⊓ b ⊔ (a ⊔ b ⊔ c)ᶜ ⊓ c) = z ⊔ (z ⊔ z) := by rw [H₁, I₁, J₁]
      _ = z := by repeat rw [ident₁]

-- We don't try to dualize the proof here, that's too painful, we apply de Morgan liberally
@[simp]
lemma assoc₂ (a b c : α) : a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c := by
  apply inv_elim
  simp

instance ShefferLE : LE α := ⟨ λ a b ↦ a = b ⊓ a ⟩

lemma Sheffer.le_refl (a : α) : a ≤ a := by simp [ShefferLE]

lemma Sheffer.le_trans (a b c : α) : a ≤ b → b ≤ c → a ≤ c := by
  rw [ShefferLE]
  intro h₁ h₂
  calc
    a = b ⊓ a       := h₁
    _ = (c ⊓ b) ⊓ a := by conv => lhs; rw [h₂]
    _ = c ⊓ (b ⊓ a) := Eq.symm (assoc₂ c b a)
    _ = c ⊓ a       := by rw [← h₁]

lemma Sheffer.le_antisymm (a b : α) : a ≤ b → b ≤ a → a = b := by
  simp [ShefferLE]
  intro h₁ h₂
  calc
    a = b ⊓ a := h₁
    _ = a ⊓ b := commut₂ ..
    _ = b     := id (Eq.symm h₂)


instance ShefferToBooleanAlg : BooleanAlgebra α where
  sup := (. ⊔ .)
  le_refl := fun a ↦ Sheffer.le_refl a
  le_trans := fun a b c a_1 a_2 ↦ Sheffer.le_trans a b c a_1 a_2
  le_antisymm := Sheffer.le_antisymm
  le_sup_left := by
    intro a b
    simp only [ShefferLE, Sup.sup]
    rw [commut₂]
    exact Eq.symm (absorb₂ a b)
  le_sup_right := by
    intro a b
    simp only [ShefferLE]
    rw [commut₂, commut₁]
    exact Eq.symm (absorb₂ b a)
  sup_le := by
    intro a b c
    simp only [ShefferLE]
    intro h₁ h₂
    calc
      a ⊔ b = (c ⊓ a) ⊔ b       := by conv => left; left; rw [h₁]
      _     = (c ⊓ a) ⊔ (c ⊓ b) := by conv => left; right; rw [h₂]
      _     = c ⊓ (a ⊔ b)       := Eq.symm (distrib₂ ..)
  inf := (. ⊓ .)
  inf_le_left := by
    intro a b; simp [ShefferLE]
  inf_le_right := by
    intro a b; simp only [ShefferLE]
    calc
      a ⊓ b = a ⊓ (b ⊓ b) := by rw [idemp₂]
      _     = a ⊓ b ⊓ b   := assoc₂ a b b
      _     = b ⊓ a ⊓ b   := by conv => left; left; rw [commut₂]
      _     = b ⊓ (a ⊓ b) := Eq.symm (assoc₂ ..)
  le_inf := by
    intro a b c h₁ h₂
    simp only [ShefferLE]
    calc
      a = b ⊓ a       := h₁
      _ = b ⊓ (c ⊓ a) := by conv => left; right; rw [h₂]
      _ = b ⊓ c ⊓ a  := by exact assoc₂ b c a
  le_sup_inf := by intro a b c; simp; rw [distrib₁]; exact Sheffer.le_refl ..
  top := u
  bot := z
  inf_compl_le_bot := by intro a; simp only [compl₂]; exact Sheffer.le_refl ..
  top_le_sup_compl := by intro a; simp only [compl₁]; exact Sheffer.le_refl ..
  le_top := by intro a; simp only [ShefferLE]; rw [commut₂]; exact Eq.symm (ident₂ a)
  bot_le := by intro a; simp [ShefferLE]

end ShefferLaws

section BooleanToSheffer

variable {α : Type*}
variable [BooleanAlgebra α]

-- This is intentionally not an instance to avoid creating an instance cycle
-- Boolean Algebra -> Sheffer Algebra -> Boolean Algebra.
def BooleanAlgToSheffer : ShefferAlgebra α where
  stroke x y := (x ⊓ y)ᶜ
  elt := ⊥
  sh₁ := by intro a; simp [prime]
  sh₂ := by intro a b; simp [prime]
  sh₃ := by intro a b c; simp [prime]; rw [inf_sup_left]
            conv => left; left; rw [inf_comm]
            conv => left; right; rw [inf_comm]

end BooleanToSheffer
-}
