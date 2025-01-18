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
(︱) :: SStroke -> SStroke -> SStroke
(︱) = uninterpret "︱"
infixl 7 ︱

-- | Negation in terms of ǀ
-- TODO: I'd like to use ﬧ instead of n here, but doctest has a bug that causes
-- the properties to be ignore. So, just using n for now. See: https://github.com/phadej/cabal-extras/issues/131
n :: SStroke -> SStroke
n x = x ︱x

-- | First Sheffer axiom @ﬧﬧa == a@
sheffer1 :: KD Proof
sheffer1 = axiom "ﬧﬧa == a" $ \(Forall @"a" a) -> n (n a) .== a

-- | Second Sheffer axiom @a ︱(b ︱ﬧb) == ﬧa@
sheffer2 :: KD Proof
sheffer2 = axiom "a ︱(b ︱ﬧb) == ﬧa" $ \(Forall @"a" a) (Forall @"b" b) -> a ︱(b ︱n b) .== n a

-- | Third Sheffer axiom @ﬧ(a ︱(b ︱c)) == (ﬧb ︱a) ︱(ﬧc ︱a)@
sheffer3 :: KD Proof
sheffer3 = axiom "ﬧ(a ︱(b ︱c)) == (ﬧb ︱a) ︱(ﬧc ︱a)"
               $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> n (a ︱(b ︱c)) .== (n b ︱a) ︱(n c ︱a)

-- * Infimum, supremum, bottom, and top

-- | Infimum: Greatest lower bound.
-- TODO: I'd like to use ⊓ here, but I can't figure out how to make that an operator.
inf :: SStroke -> SStroke -> SStroke
a `inf` b = n a ︱n b

-- | Supremum: Least upper bound.
-- TODO: I'd like to use ⊔ here, but I can't figure out how to make that an operator.
sup :: SStroke -> SStroke -> SStroke
a `sup` b = n (a ︱b)

-- | The unique bottom element
z :: SStroke
z = elt ︱n elt
 where elt = uninterpret "z"

-- | The unique top element
u :: SStroke
u = n z

-- * Sheffer's stroke defines a boolean algebra

-- | Prove that Sheffer stroke axioms imply it is a boolean algebra. We have:
--
-- TODO: Due to doctest issues, the output here does not get tested.
-- >>> shefferBooleanAlgebra
shefferBooleanAlgebra :: IO Proof
shefferBooleanAlgebra = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

  sh1 <- sheffer1
  sh2 <- sheffer2
  sh3 <- sheffer3

  -- @a ︱b == b ︱a@
  commut <- chainLemma "a ︱b == b ︱a"
                       (\(Forall @"a" a) (Forall @"b" b) -> a ︱b .== b ︱a)
                       (pure ())
                       (\a b -> [ a ︱b
                                , n (n (a ︱b))
                                , n (n (a ︱n (n b)))
                                , n (n (n (n b) ︱ a))
                                , b ︱ a
                                ])
                       [sh1, sh3]

  -- @a ︱ﬧa == b ︱ﬧb@
  -- Make sure this is used
  _all_bot <- chainLemma "a ︱ﬧa == b ︱ﬧb"
                         (\(Forall @"a" a) (Forall @"b" b) -> a ︱n a .== b ︱n b)
                         (pure ())
                         (\a b -> [ a ︱n a
                                  , n ((a ︱n a) ︱(b ︱n b))
                                  , n ((b ︱n b) ︱(a ︱n a))
                                  , n (n (b ︱n b))
                                  , b ︱ n b
                                  ])
                         [sh1, sh2, commut]

  -- @a ⊔ b == b ⊔ a@
  commut1 <- lemma "a ⊔ b == b ⊔ a"
                   (\(Forall @"a" a) (Forall @"b" b) -> a `sup` b .== b `sup` a)
                   [commut]

  -- @a ⊓ b == b ⊓ a@
  commut2 <- lemma "a ⊓ b == b ⊓ a"
                   (\(Forall @"a" a) (Forall @"b" b) -> a `inf` b .== b `inf` a)
                   [commut]

  -- @a ⊔ z == a@
  ident1 <- lemma "a ⊔ z = a"
                  (\(Forall @"a" a) -> a `sup` z .== a)
                  [sh1, sh2]

  -- @a ⊓ u == a@
  ident2 <- lemma "a ⊓ u = a"
                  (\(Forall @"a" a) -> a `inf` u .== a)
                  [sh1, sh2]

  -- @a ⊔ (b ⊓ c) == (a ⊔ b) ⊓ (a ⊔ c)@
  distrib1 <- lemma "a ⊔ (b ⊓ c) == (a ⊔ b) ⊓ (a ⊔ c)"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a `sup` (b `inf` c) .== (a `sup` b) `inf` (a `sup` c))
                    [sh1, sh3, commut]

  -- @a ⊓ (b ⊔ c) == (a ⊓ b) ⊔ (a ⊓ c)@
  distrib2 <- lemma "a ⊓ (b ⊔ c) == (a ⊓ b) ⊔ (a ⊓ c)"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a `inf` (b `sup` c) .== (a `inf` b) `sup` (a `inf` c))
                    [sh1, sh3, commut]

  -- @a ⊔ n a == u@
  compl1 <- lemma "a ⊔ ﬧa == u"
                  (\(Forall @"a" a) -> a `sup` n a .== u)
                  [sh1, sh2, sh3]

  -- @a ⊓ ﬧa == z@
  compl2 <- lemma "a ⊓ ﬧa == z"
                  (\(Forall @"a" a) -> a `inf` n a .== z)
                  [sh1, sh2, sh3]

  -- @a ⊔ u == u@
  bound1 <- chainLemma "a ⊔ u"
                       (\(Forall @"a" a) -> a `sup` u .== u)
                       (pure ())
                       (\a -> [ a `sup` u
                              , (a `sup` u) `inf` u
                              , u `inf` (a `sup` u)
                              , (a `sup` n a) `inf` (a `sup` u)
                              , a `sup` (n a `inf` u)
                              , a `sup` n a
                              , u
                              ])
                       [ident2, commut2, compl1, distrib1]

  -- @a ⊓ z = z@
  bound2 <- chainLemma "a ⊓ z = z"
                       (\(Forall @"a" a) -> a `inf` z .== z)
                       (pure ())
                       (\a -> [ a `inf` z
                              , (a `inf` z) `sup` z
                              , z `sup` (a `inf` z)
                              , (a `inf` n a) `sup` (a `inf` z)
                              , a `inf` (n a `sup` z)
                              , a `inf` n a
                              , z
                              ])
                       [ident1, commut1, compl2, distrib2, ident1, compl2]

  -- @a ⊔ (a ⊓ b) = a@
  -- TODO: Make sure this is used
  _absorb1 <- chainLemma "a ⊔ (a ⊓ b) = a"
                        (\(Forall @"a" a) (Forall @"b" b) -> a `sup` (a `inf` b) .== a)
                        (pure ())
                        (\a b -> [ a `sup` (a `inf` b)
                                 , (a `inf` u) `sup` (a `inf` b)
                                 , a `inf` (u `sup` b)
                                 , a `inf` (b `sup` u)
                                 , a `inf` u
                                 , a
                                 ])
                        [ident2, distrib2, commut1, bound1]

  -- @a ⊓ (a ⊔ b) = a@
  -- TODO: Make sure this is used
  _absorb2 <- chainLemma "a ⊓ (a ⊔ b) = a"
                         (\(Forall @"a" a) (Forall @"b" b) -> a `inf` (a `sup` b) .== a)
                         (pure ())
                         (\a b -> [ a `inf` (a `sup` b)
                                  , (a `sup` z) `inf` (a `sup` b)
                                  , a `sup` (z `inf` b)
                                  , a `sup` (b `inf` z)
                                  , a `sup` z
                                  , a
                                  ])
                        [ident1, distrib1, commut2, bound2]

  pure sorry

{-

@[simp] -- This simp is a little overeager.
-- it would be nice to have a "dualization" tactic. This might be some work though.
@[simp] -- This simp is a little overeager.
lemma absorb₂ (a b : α) : a ⊓ (a ⊔ b) = a := by
  calc
    a ⊓ (a ⊔ b) = (a ⊔ z) ⊓ (a ⊔ b) := by rw [ident₁]
    _           = a ⊔ (z ⊓ b)       := by rw [distrib₁]
    _           = a ⊔ (b ⊓ z)       := by conv => lhs; rw [commut₂]
    _           = a ⊔ z             := by rw [bound₂]
    _           = a                 := ident₁ a

@[simp]
lemma idemp₂ (a : α) : a ⊓ a = a := by
  symm
  calc
    a = a ⊓ (a ⊔ z) := Eq.symm (absorb₂ a z)
    _ = a ⊓ a       := by rw [ident₁]

lemma inv (a a' : α) : a ⊔ a' = u → a ⊓ a' = z → a' = aᶜ := by
  intro h₁ h₂
  calc
    a' = a' ⊓ u               := Eq.symm (ident₂ a')
    _  = a' ⊓ (a ⊔ aᶜ)        := by rw [compl₁]
    _  = (a' ⊓ a) ⊔ (a' ⊓ aᶜ) := by rw [distrib₂]
    _  = (a' ⊓ a) ⊔ (aᶜ ⊓ a') := by conv => left; right; exact commut₂ a' aᶜ
    _  = (a ⊓ a') ⊔ (aᶜ ⊓ a') := by conv => left; left; exact commut₂ a' a
    _  = z ⊔ (aᶜ ⊓ a')        := by rw [h₂]
    _  = (a ⊓ aᶜ) ⊔ (aᶜ ⊓ a') := by rw [compl₂]
    _  = (aᶜ ⊓ a) ⊔ (aᶜ ⊓ a') := by conv => left; left; exact commut₂ a aᶜ
    _  = aᶜ ⊓ (a ⊔ a')        := by rw [distrib₂]
    _  = aᶜ ⊓ u               := by rw [h₁]
    _  = aᶜ                   := ident₂ aᶜ

lemma dne (a : α) : aᶜᶜ = a := by
  symm
  apply inv
  . rw [commut₁]; exact compl₁ a
  . rw [commut₂]; exact compl₂ a

lemma inv_elim (a b : α) : aᶜ = bᶜ → a = b := by
  intro h
  have h' : aᶜᶜ = bᶜᶜ := congrArg compl h
  simp only [dne] at h'
  trivial

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
