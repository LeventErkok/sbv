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
 where elt = some "z" (const sTrue)

-- | The unique top element
u :: SStroke
u = ﬧ z

-- * Sheffer's stroke defines a boolean algebra

-- | Prove that Sheffer stroke axioms imply it is a boolean algebra. We have:
--
-- TODO: Due to doctest issues, the output here does not get tested.
-- See: https://github.com/yav/haskell-lexer/issues/14, which seems to be the root cause.
-- Make a proper test for this using the regular test infrastructure
-- >>> shefferBooleanAlgebra
shefferBooleanAlgebra :: IO Proof
shefferBooleanAlgebra = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

  sh1 <- sheffer1
  sh2 <- sheffer2
  sh3 <- sheffer3

  commut <- chainLemma "a | b = b | a"
                       (\(Forall @"a" a) (Forall @"b" b) -> a ⏐ b .== b ⏐ a)
                       (\a b -> (sTrue, [ a ⏐ b
                                        , ﬧ (ﬧ (a ⏐ b))
                                        , ﬧ (ﬧ (a ⏐ ﬧ (ﬧ b)))
                                        , ﬧ (ﬧ (ﬧ (ﬧ b) ⏐ a))
                                        , b ⏐ a
                                        ]))
                       [sh1, sh3]

  all_bot <- chainLemma "a | a′ = b | b′"
                        (\(Forall @"a" a) (Forall @"b" b) -> a ⏐ ﬧ a .== b ⏐ ﬧ b)
                        (\a b -> (sTrue, [ a ⏐ ﬧ a
                                         , ﬧ ((a ⏐ ﬧ a) ⏐ (b ⏐ ﬧ b))
                                         , ﬧ ((b ⏐ ﬧ b) ⏐ (a ⏐ ﬧ a))
                                         , ﬧ (ﬧ (b ⏐ ﬧ b))
                                         , b ⏐ ﬧ b
                                         ]))
                        [sh1, sh2, commut]

  commut1 <- lemma "a ⊔ b = b ⊔ a"
                   (\(Forall @"a" a) (Forall @"b" b) -> a ⨆ b .== b ⨆ a)
                   [commut]

  commut2 <- lemma "a ⊓ b = b ⊓ a"
                   (\(Forall @"a" a) (Forall @"b" b) -> a ⨅ b .== b ⨅ a)
                   [commut]

  ident1 <- lemma "a ⊔ z = a"
                  (\(Forall @"a" a) -> a ⨆ z .== a)
                  [sh1, sh2]

  ident2 <- lemma "a ⊓ u = a"
                  (\(Forall @"a" a) -> a ⨅ u .== a)
                  [sh1, sh2]

  distrib1 <- lemma "a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a ⨆ (b ⨅ c) .== (a ⨆ b) ⨅ (a ⨆ c))
                    [sh1, sh3, commut]

  distrib2 <- lemma "a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a ⨅ (b ⨆ c) .== (a ⨅ b) ⨆ (a ⨅ c))
                    [sh1, sh3, commut]

  compl1 <- lemma "a ⊔ aᶜ = u"
                  (\(Forall @"a" a) -> a ⨆ ﬧ a .== u)
                  [sh1, sh2, sh3, all_bot]

  compl2 <- lemma "a ⊓ aᶜ = z"
                  (\(Forall @"a" a) -> a ⨅ ﬧ a .== z)
                  [sh1, commut, all_bot]

  bound1 <- chainLemma "a ⊔ u = u"
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

  bound2 <- chainLemma "a ⊓ z = z"
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

  absorb1 <- chainLemma "a ⊔ (a ⊓ b) = a"
                        (\(Forall @"a" a) (Forall @"b" b) -> a ⨆ (a ⨅ b) .== a)
                        (\a b -> (sTrue, [ a ⨆ (a ⨅ b)
                                         , (a ⨅ u) ⨆ (a ⨅ b)
                                         , a ⨅ (u ⨆ b)
                                         , a ⨅ (b ⨆ u)
                                         , a ⨅ u
                                         , a
                                         ]))
                        [ident2, distrib2, commut1, bound1]

  absorb2 <- chainLemma "a ⊓ (a ⊔ b)"
                        (\(Forall @"a" a) (Forall @"b" b) -> a ⨅ (a ⨆ b) .== a)
                        (\a b -> (sTrue, [ a ⨅ (a ⨆ b)
                                         , (a ⨆ z) ⨅ (a ⨆ b)
                                         , a ⨆ (z ⨅ b)
                                         , a ⨆ (b ⨅ z)
                                         , a ⨆ z
                                         , a
                                         ]))
                        [ident1, distrib1, commut2, bound2]

  idemp2 <- chainLemma "a ⊓ a = a"
                       (\(Forall @"a" a) -> a ⨅ a .== a)
                       (\a -> (sTrue, [ a ⨅ a
                                      , a ⨅ (a ⨆ z)
                                      , a
                                      ]))
                       [ident1, absorb2]

  inv <- chainLemma "a ⊔ a' = u → a ⊓ a' = z → a' = aᶜ"
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

  dne <- lemma "aᶜᶜ = a"
               (\(Forall @"a" a) -> ﬧ (ﬧ a) .== a)
               [inv, compl1, compl2, commut1, commut2]

  inv_elim <- lemma "aᶜ = bᶜ → a = b"
                    (\(Forall @"a" a) (Forall @"b" b) -> ﬧ a .== ﬧ b .=> a .== b)
                    [dne]

  cancel <- lemma "a ⊔ bᶜ = u → a ⊓ bᶜ = z → a = b"
                  (\(Forall @"a" a) (Forall @"b" b) -> a ⨆ ﬧ b .== u .=> a ⨅ ﬧ b .== z .=> a .== b)
                  [inv, inv_elim]

  a1 <- chainLemma "a ⊔ (aᶜ ⊔ b) = u"
                   (\(Forall @"a" a) (Forall @"b" b) -> a ⨆ (ﬧ a ⨆ b) .== u)
                   (\a b -> (sTrue, [ a ⨆ (ﬧ a ⨆ b)
                                    , (a ⨆ (ﬧ a ⨆ b)) ⨅ u
                                    , u ⨅ (a ⨆ (ﬧ a ⨆ b))
                                    , (a ⨆ ﬧ a) ⨅ (a ⨆ (ﬧ a ⨆ b))
                                    , a ⨆ (ﬧ a ⨅ (ﬧ a ⨆ b))
                                    , a ⨆ ﬧ a
                                    , u
                                    ]))
                   [ident2, commut2, compl1, distrib1, absorb2]

  a2 <- chainLemma "a ⊓ (aᶜ ⊓ b) = z"
                   (\(Forall @"a" a) (Forall @"b" b) -> a ⨅ (ﬧ a ⨅ b) .== z)
                   (\a b -> (sTrue, [ a ⨅ (ﬧ a ⨅ b)
                                    , (a ⨅ (ﬧ a ⨅ b)) ⨆ z
                                    , z ⨆ (a ⨅ (ﬧ a ⨅ b))
                                    , (a ⨅ ﬧ a) ⨆ (a ⨅ (ﬧ a ⨅ b))
                                    , a ⨅ (ﬧ a ⨆ (ﬧ a ⨅ b))
                                    , a ⨅ ﬧ a
                                    , z
                                    ]))
                   [ident1, commut1, compl2, distrib2, absorb1]

  dm1 <- lemma "(a ⊔ b)ᶜ = aᶜ ⊓ bᶜ"
               (\(Forall @"a" a) (Forall @"b" b) -> ﬧ(a ⨆ b) .== ﬧ a ⨅ ﬧ b)
               [a1, a2, dne, commut1, commut2, ident1, ident2, distrib1, distrib2]

  dm2 <- lemma "(a ⨅ b)ᶜ = aᶜ ⨆ bᶜ"
               (\(Forall @"a" a) (Forall @"b" b) -> ﬧ(a ⨅ b) .== ﬧ a ⨆ ﬧ b)
               [a1, a2, dne, commut1, commut2, ident1, ident2, distrib1, distrib2]


  d1 <- lemma "(a ⊔ (b ⊔ c)) ⊔ aᶜ = u"
              (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> (a ⨆ (b ⨆ c)) ⨆ ﬧ a .== u)
              [a1, a2, commut1, ident1, ident2, distrib1, compl1, compl2, dm1, dm2, idemp2]

  e1 <- lemma "b ⊓ (a ⊔ (b ⊔ c)) = b"
              (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> b ⨅ (a ⨆ (b ⨆ c)) .== b)
              [distrib2, absorb1, absorb2, commut1]

  e2 <- lemma "b ⊔ (a ⊓ (b ⊓ c)) = b"
              (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> b ⨆ (a ⨅ (b ⨅ c)) .== b)
              [distrib1, absorb1, absorb2, commut2]

  f1 <- chainLemma "(a ⊔ (b ⊔ c)) ⊔ bᶜ = u"
                   (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> (a ⨆ (b ⨆ c)) ⨆ ﬧ b .== u)
                   (\a b c -> (sTrue, [ (a ⨆ (b ⨆ c)) ⨆ ﬧ b
                                      , ﬧ b ⨆ (a ⨆ (b ⨆ c))
                                      , u ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c)))
                                      , (b ⨆ ﬧ b) ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c)))
                                      , (ﬧ b ⨆ b) ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c)))
                                      , ﬧ b ⨆ (b ⨅ (a ⨆ (b ⨆ c)))
                                      , ﬧ b ⨆ b
                                      , u
                                      ]))
                   [commut1, commut2, distrib1, e1, compl1, compl2]

  g1 <- lemma "(a ⊔ (b ⊔ c)) ⊔ cᶜ = u"
              (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> (a ⨆ (b ⨆ c)) ⨆ ﬧ c .== u)
              [commut1, f1]

  h1 <- chainLemma "(a ⊔ b ⊔ c)ᶜ ⊓ a = z"
                   (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> ﬧ (a ⨆ b ⨆ c) ⨅ a .== z)
                   (\a b c -> (sTrue, [ a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)
                                      , (a ⨅  (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)) ⨆ z
                                      , z ⨆ (a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))
                                      , (a ⨅ ﬧ a) ⨆ (a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))
                                      , a ⨅ (ﬧ a ⨆ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))
                                      , a ⨅ (ﬧ a ⨆ (ﬧ c ⨅ (ﬧ a ⨅ ﬧ b)))
                                      , a ⨅ ﬧ a
                                      , z
                                      ]))
                   [ident1, commut1, commut2, compl2, distrib2, e2]

  i1 <- lemma "(a ⊔ b ⊔ c)ᶜ ⊓ b = z"
              (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> ﬧ (a ⨆ b ⨆ c) ⨅ b .== z)
              [commut1, h1]

  j1 <- lemma "(a ⊔ b ⊔ c)ᶜ ⊓ c = z"
              (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> ﬧ (a ⨆ b ⨆ c) ⨅ c .== z)
              [a2, dne, commut2]

  assoc1 <- do
    c1 <- chainLemma "(a ⊔ (b ⊔ c)) ⊔ ((a ⊔ b) ⊔ c)ᶜ = u"
                     (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> (a ⨆ (b ⨆ c)) ⨆ ﬧ((a ⨆ b) ⨆ c) .== u)
                     (\a b c -> (sTrue, [ (a ⨆ (b ⨆ c)) ⨆ ﬧ((a ⨆ b) ⨆ c)
                                        , (a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)
                                        , ((a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b)) ⨅ ((a ⨆ (b ⨆ c)) ⨆ ﬧ c)
                                        , u
                                        ]))
                     [dm1, distrib1, d1, f1, g1]

    c2 <- chainLemma "(a ⊔ (b ⊔ c)) ⊓ ((a ⊔ b) ⊔ c)ᶜ = z"
                     (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> (a ⨆ (b ⨆ c)) ⨅ ﬧ((a ⨆ b) ⨆ c) .== z)
                     (\a b c -> (sTrue, [ (a ⨆ (b ⨆ c)) ⨅ ﬧ((a ⨆ b) ⨆ c)
                                        , (a ⨅ ﬧ((a ⨆ b) ⨆ c)) ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c))
                                        , (ﬧ((a ⨆ b) ⨆ c) ⨅ a) ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c))
                                        , z ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c))
                                        , ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)) ⨆ z
                                        , (b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)
                                        , ﬧ((a ⨆ b) ⨆ c) ⨅ (b ⨆ c)
                                        ]))
                     [commut1, commut2, distrib2, h1, d1, ident1]

    lemma "a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c"
          (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a ⨆ (b ⨆ c) .== (a ⨆ b) ⨆ c)
          [c1, c2, cancel]


  lemma "TODO" sFalse [assoc1, i1, j1]

{-
-- Incredibly, these are derivable
@[simp]
lemma assoc₁ (a b c : α) : a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c := by
  apply cancel; simp
  . calc
      (a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ ⊓ cᶜ) = ((a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ)) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) := by rw [distrib₁]
      _                              = ((a ⊔ (b ⊔ c) ⊔ aᶜ) ⊓ ((a ⊔ (b ⊔ c) ⊔ bᶜ))) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) := by rw [distrib₁]
      _                              = (u ⊓ u) ⊓ u := by rw [D₁, F₁, G₁]
      _                              = u := by simp
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
