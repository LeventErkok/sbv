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
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.ShefferStroke where

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
  show p = unlines [ "BooleanAlgebraProof {"
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
#define A      (Forall @"a"  (a  :: SStroke))
#define AAp A  (Forall @"a'" (a' :: SStroke))
#define AB  A  (Forall @"b"  (b  :: SStroke))
#define ABC AB (Forall @"c"  (c  :: SStroke))

-- | First Sheffer axiom @ﬧﬧa == a@
sheffer1 :: KD Proof
sheffer1 = axiom "ﬧﬧa == a" $ \A -> ﬧﬧ a .== a

-- | Second Sheffer axiom @a ⏐ (b ⏐ ﬧb) == ﬧa@
sheffer2 :: KD Proof
sheffer2 = axiom "a ⏐ (b ⏐ ﬧb) == ﬧa" $ \AB -> a ⏐ (b ⏐ ﬧ b) .== ﬧ a

-- | Third Sheffer axiom @ﬧ(a ⏐ (b ⏐ c)) == (ﬧb ⏐ a) ⏐ (ﬧc ⏐ a)@
sheffer3 :: KD Proof
sheffer3 = axiom "ﬧ(a ⏐ (b ⏐ c)) == (ﬧb ⏐ a) ⏐ (ﬧc ⏐ a)" $ \ABC -> ﬧ(a ⏐ (b ⏐ c)) .== (ﬧ b ⏐ a) ⏐ (ﬧ c ⏐ a)

-- * Sheffer's stroke defines a boolean algebra

-- | Prove that Sheffer stroke axioms imply it is a boolean algebra. We have:
--
-- TODO: Due to doctest issues, the output here does not get tested.
-- See: https://github.com/yav/haskell-lexer/issues/14, which seems to be the root cause.
-- Make a proper test for this using the regular test infrastructure
-- >>> shefferBooleanAlgebra
shefferBooleanAlgebra :: IO BooleanAlgebraProof
shefferBooleanAlgebra = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60, measureTime = True}} $ do

  -- Get the axioms
  sh1 <- sheffer1
  sh2 <- sheffer2
  sh3 <- sheffer3

  commut <- chainLemma "a | b = b | a"
                       (\AB -> a ⏐ b .== b ⏐ a)
                       (\a b -> (sTrue, [ a ⏐ b
                                        , ﬧﬧ(a ⏐ b)
                                        , ﬧﬧ(a ⏐ ﬧﬧ b)
                                        , ﬧﬧ((ﬧﬧ b) ⏐ a)
                                        , b ⏐ a
                                        ]))
                       [sh1, sh3]

  all_bot <- chainLemma "a | a′ = b | b′"
                        (\AB -> a ⏐ ﬧ a .== b ⏐ ﬧ b)
                        (\a b -> (sTrue, [ a ⏐ ﬧ a
                                         , ﬧ((a ⏐ ﬧ a) ⏐ (b ⏐ ﬧ b))
                                         , ﬧ((b ⏐ ﬧ b) ⏐ (a ⏐ ﬧ a))
                                         , ﬧﬧ(b ⏐ ﬧ b)
                                         , b ⏐ ﬧ b
                                         ]))
                        [sh1, sh2, commut]

  commut1  <- lemma "a ⊔ b = b ⊔ a" (\AB -> a ⨆ b .== b ⨆ a) [commut]
  commut2  <- lemma "a ⊓ b = b ⊓ a" (\AB -> a ⨅ b .== b ⨅ a) [commut]

  ident1   <- lemma "a ⊔ ⲳ = a" (\A  -> a ⨆ ⲳ .== a) [sh1, sh2]
  ident2   <- lemma "a ⊓ т = a" (\A  -> a ⨅ т .== a) [sh1, sh2]

  distrib1 <- lemma "a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)" (\ABC -> a ⨆ (b ⨅ c) .== (a ⨆ b) ⨅ (a ⨆ c)) [sh1, sh3, commut]
  distrib2 <- lemma "a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)" (\ABC -> a ⨅ (b ⨆ c) .== (a ⨅ b) ⨆ (a ⨅ c)) [sh1, sh3, commut]

  compl1 <- lemma "a ⊔ aᶜ = т" (\A -> a ⨆ ﬧ a .== т) [sh1, sh2, sh3, all_bot]
  compl2 <- lemma "a ⊓ aᶜ = ⲳ" (\A -> a ⨅ ﬧ a .== ⲳ) [sh1, commut, all_bot]

  bound1 <- chainLemma "a ⊔ т = т"
                       (\A -> a ⨆ т .== т)
                       (\a -> (sTrue, [ a ⨆ т
                                      , (a ⨆ т) ⨅ т
                                      , т ⨅ (a ⨆ т)
                                      , (a ⨆ ﬧ a) ⨅ (a ⨆ т)
                                      , a ⨆ (ﬧ a ⨅ т)
                                      , a ⨆ ﬧ a
                                      , т :: SStroke
                                      ]))
                       [ident2, commut2, compl1, distrib1]

  bound2 <- chainLemma "a ⊓ ⲳ = ⲳ"
                       (\A -> a ⨅ ⲳ .== ⲳ)
                       (\a -> (sTrue, [ a ⨅ ⲳ
                                      , (a ⨅ ⲳ) ⨆ ⲳ
                                      , ⲳ ⨆ (a ⨅ ⲳ)
                                      , (a ⨅ ﬧ a) ⨆ (a ⨅ ⲳ)
                                      , a ⨅ (ﬧ a ⨆ ⲳ)
                                      , a ⨅ ﬧ a
                                      , ⲳ :: SStroke
                                      ]))
                       [ident1, commut1, compl2, distrib2, ident1, compl2]

  absorb1 <- chainLemma "a ⊔ (a ⊓ b) = a"
                        (\AB -> a ⨆ (a ⨅ b) .== a)
                        (\a b -> (sTrue, [ a ⨆ (a ⨅ b)
                                         , (a ⨅ т) ⨆ (a ⨅ b)
                                         , a ⨅ (т ⨆ b)
                                         , a ⨅ (b ⨆ т)
                                         , a ⨅ т
                                         , a :: SStroke
                                         ]))
                        [ident2, distrib2, commut1, bound1]

  absorb2 <- chainLemma "a ⊓ (a ⊔ b)"
                        (\AB -> a ⨅ (a ⨆ b) .== a)
                        (\a b -> (sTrue, [ a ⨅ (a ⨆ b)
                                         , (a ⨆ ⲳ) ⨅ (a ⨆ b)
                                         , a ⨆ (ⲳ ⨅ b)
                                         , a ⨆ (b ⨅ ⲳ)
                                         , a ⨆ ⲳ
                                         , a :: SStroke
                                         ]))
                        [ident1, distrib1, commut2, bound2]

  idemp2 <- chainLemma "a ⊓ a = a"
                       (\A -> a ⨅ a .== a)
                       (\a -> (sTrue, [ a ⨅ a
                                      , a ⨅ (a ⨆ ⲳ)
                                      , a :: SStroke
                                      ]))
                       [ident1, absorb2]

  inv <- chainLemma "a ⊔ a' = т → a ⊓ a' = ⲳ → a' = aᶜ"
                    (\AAp  -> a ⨆ a' .== т .=> a ⨅ a' .== ⲳ .=> a' .== ﬧ a)
                    (\a a' -> (a ⨆ a' .== т .&& a ⨅ a' .== ⲳ, [ a'
                                                              , a' ⨅ т
                                                              , a' ⨅ (a ⨆ ﬧ a)
                                                              , (a' ⨅ a) ⨆ (a' ⨅ ﬧ a)
                                                              , (a' ⨅ a) ⨆ (ﬧ a ⨅ a')
                                                              , (a ⨅ a') ⨆ (ﬧ a ⨅ a')
                                                              , ⲳ ⨆ (ﬧ a ⨅ a')
                                                              , (a ⨅ ﬧ a) ⨆ (ﬧ a ⨅ a')
                                                              , (ﬧ a ⨅ a) ⨆ (ﬧ a ⨅ a')
                                                              , ﬧ a ⨅ (a ⨆ a')
                                                              , ﬧ a ⨅ т
                                                              , ﬧ a :: SStroke
                                                              ]))
                    [ident2, compl1, distrib2, commut2]

  dne      <- lemma "aᶜᶜ = a"         (\A -> ﬧﬧ a .== a)               [inv, compl1, compl2, commut1, commut2]
  inv_elim <- lemma "aᶜ = bᶜ → a = b" (\AB -> ﬧ a .== ﬧ b .=> a .== b) [dne]

  cancel <- lemma "a ⊔ bᶜ = т → a ⊓ bᶜ = ⲳ → a = b" (\AB -> a ⨆ ﬧ b .== т .=> a ⨅ ﬧ b .== ⲳ .=> a .== b) [inv, inv_elim]

  a1 <- chainLemma "a ⊔ (aᶜ ⊔ b) = т"
                   (\AB  -> a ⨆ (ﬧ a ⨆ b) .== т)
                   (\a b -> (sTrue, [ a ⨆ (ﬧ a ⨆ b)
                                    , (a ⨆ (ﬧ a ⨆ b)) ⨅ т
                                    , т ⨅ (a ⨆ (ﬧ a ⨆ b))
                                    , (a ⨆ ﬧ a) ⨅ (a ⨆ (ﬧ a ⨆ b))
                                    , a ⨆ (ﬧ a ⨅ (ﬧ a ⨆ b))
                                    , a ⨆ ﬧ a
                                    , т :: SStroke
                                    ]))
                   [ident2, commut2, compl1, distrib1, absorb2]

  a2 <- chainLemma "a ⊓ (aᶜ ⊓ b) = ⲳ"
                   (\AB  -> a ⨅ (ﬧ a ⨅ b) .== ⲳ)
                   (\a b -> (sTrue, [ a ⨅ (ﬧ a ⨅ b)
                                    , (a ⨅ (ﬧ a ⨅ b)) ⨆ ⲳ
                                    , ⲳ ⨆ (a ⨅ (ﬧ a ⨅ b))
                                    , (a ⨅ ﬧ a) ⨆ (a ⨅ (ﬧ a ⨅ b))
                                    , a ⨅ (ﬧ a ⨆ (ﬧ a ⨅ b))
                                    , a ⨅ ﬧ a
                                    , ⲳ :: SStroke
                                    ]))
                   [ident1, commut1, compl2, distrib2, absorb1]

  dm1 <- lemma "(a ⊔ b)ᶜ = aᶜ ⊓ bᶜ"
               (\AB -> ﬧ(a ⨆ b) .== ﬧ a ⨅ ﬧ b)
               [a1, a2, dne, commut1, commut2, ident1, ident2, distrib1, distrib2]

  dm2 <- lemma "(a ⨅ b)ᶜ = aᶜ ⨆ bᶜ"
               (\AB -> ﬧ(a ⨅ b) .== ﬧ a ⨆ ﬧ b)
               [a1, a2, dne, commut1, commut2, ident1, ident2, distrib1, distrib2]


  d1 <- lemma "(a ⊔ (b ⊔ c)) ⊔ aᶜ = т"
              (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ a .== т)
              [a1, a2, commut1, ident1, ident2, distrib1, compl1, compl2, dm1, dm2, idemp2]

  e1 <- lemma "b ⊓ (a ⊔ (b ⊔ c)) = b"
              (\ABC -> b ⨅ (a ⨆ (b ⨆ c)) .== b)
              [distrib2, absorb1, absorb2, commut1]

  e2 <- lemma "b ⊔ (a ⊓ (b ⊓ c)) = b"
              (\ABC -> b ⨆ (a ⨅ (b ⨅ c)) .== b)
              [distrib1, absorb1, absorb2, commut2]

  f1 <- chainLemma "(a ⊔ (b ⊔ c)) ⊔ bᶜ = т"
                   (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ b .== т)
                   (\a b c -> (sTrue, [ (a ⨆ (b ⨆ c)) ⨆ ﬧ b
                                      , ﬧ b ⨆ (a ⨆ (b ⨆ c))
                                      , т ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c)))
                                      , (b ⨆ ﬧ b) ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c)))
                                      , (ﬧ b ⨆ b) ⨅ (ﬧ b ⨆ (a ⨆ (b ⨆ c)))
                                      , ﬧ b ⨆ (b ⨅ (a ⨆ (b ⨆ c)))
                                      , ﬧ b ⨆ b
                                      , т :: SStroke
                                      ]))
                   [commut1, commut2, distrib1, e1, compl1, compl2]

  g1 <- lemma "(a ⊔ (b ⊔ c)) ⊔ cᶜ = т"
              (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ c .== т)
              [commut1, f1]

  h1 <- chainLemma "(a ⊔ b ⊔ c)ᶜ ⊓ a = ⲳ"
                   (\ABC -> ﬧ(a ⨆ b ⨆ c) ⨅ a .== ⲳ)
                   (\a b c -> (sTrue, [ a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)
                                      , (a ⨅  (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)) ⨆ ⲳ
                                      , ⲳ ⨆ (a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))
                                      , (a ⨅ ﬧ a) ⨆ (a ⨅ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))
                                      , a ⨅ (ﬧ a ⨆ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c))
                                      , a ⨅ (ﬧ a ⨆ (ﬧ c ⨅ (ﬧ a ⨅ ﬧ b)))
                                      , a ⨅ ﬧ a
                                      , ⲳ :: SStroke
                                      ]))
                   [ident1, commut1, commut2, compl2, distrib2, e2]

  i1 <- lemma "(a ⊔ b ⊔ c)ᶜ ⊓ b = ⲳ" (\ABC -> ﬧ(a ⨆ b ⨆ c) ⨅ b .== ⲳ) [commut1, h1]
  j1 <- lemma "(a ⊔ b ⊔ c)ᶜ ⊓ c = ⲳ" (\ABC -> ﬧ(a ⨆ b ⨆ c) ⨅ c .== ⲳ) [a2, dne, commut2]

  assoc1 <- do
    c1 <- chainLemma "(a ⊔ (b ⊔ c)) ⊔ ((a ⊔ b) ⊔ c)ᶜ = т"
                     (\ABC -> (a ⨆ (b ⨆ c)) ⨆ ﬧ((a ⨆ b) ⨆ c) .== т)
                     (\a b c -> (sTrue, [ (a ⨆ (b ⨆ c)) ⨆ ﬧ((a ⨆ b) ⨆ c)
                                        , (a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b ⨅ ﬧ c)
                                        , ((a ⨆ (b ⨆ c)) ⨆ (ﬧ a ⨅ ﬧ b)) ⨅ ((a ⨆ (b ⨆ c)) ⨆ ﬧ c)
                                        , т :: SStroke
                                        ]))
                     [dm1, distrib1, d1, f1, g1]

    c2 <- chainLemma "(a ⊔ (b ⊔ c)) ⊓ ((a ⊔ b) ⊔ c)ᶜ = ⲳ"
                     (\ABC -> (a ⨆ (b ⨆ c)) ⨅ ﬧ((a ⨆ b) ⨆ c) .== ⲳ)
                     (\a b c -> (sTrue, [ (a ⨆ (b ⨆ c)) ⨅ ﬧ((a ⨆ b) ⨆ c)
                                        , (a ⨅ ﬧ((a ⨆ b) ⨆ c)) ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c))
                                        , (ﬧ((a ⨆ b) ⨆ c) ⨅ a) ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c))
                                        , ⲳ ⨆ ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c))
                                        , ((b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)) ⨆ ⲳ
                                        , (b ⨆ c) ⨅ ﬧ((a ⨆ b) ⨆ c)
                                        , ﬧ((a ⨆ b) ⨆ c) ⨅ (b ⨆ c)
                                        , (ﬧ((a ⨆ b) ⨆ c) ⨅ b) ⨆ (ﬧ((a ⨆ b) ⨆ c) ⨅ c)
                                        , (ﬧ((a ⨆ b) ⨆ c) ⨅ b) ⨆ ⲳ
                                        , ⲳ ⨆ ⲳ
                                        , ⲳ :: SStroke
                                        ]))
                     [commut1, commut2, distrib2, h1, d1, j1, ident1]

    lemma "a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c"
          (\ABC -> a ⨆ (b ⨆ c) .== (a ⨆ b) ⨆ c)
          [c1, c2, cancel]

  assoc2 <- do
     ie <- chainLemma "(a ⊓ (b ⊓ c))ᶜ = ((a ⊓ b) ⊓ c)ᶜ"
                      (\ABC -> ﬧ(a ⨅ (b ⨅ c)) .== ﬧ((a ⨅ b) ⨅ c))
                      (\a b c -> (sTrue, [ ﬧ(a ⨅ (b ⨅ c))
                                         , ﬧ a ⨆ ﬧ(b ⨅ c)
                                         , ﬧ a ⨆ (ﬧ b ⨆ ﬧ c)
                                         , (ﬧ a ⨆ ﬧ b) ⨆ ﬧ c
                                         , ﬧ(a ⨅ b) ⨆ ﬧ c
                                         , ﬧ((a ⨅ b) ⨅ c) :: SStroke
                                         ]))
                      [dm2, assoc1]

     chainLemma "a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c"
                (\ABC -> a ⨅ (b ⨅ c) .== (a ⨅ b) ⨅ c)
                (\a b c -> (sTrue, [ a ⨅ (b ⨅ c)
                                   , ﬧﬧ(a ⨅ (b ⨅ c))
                                   , ﬧﬧ((a ⨅ b) ⨅ c)
                                   , ((a ⨅ b) ⨅ c) :: SStroke
                                   ]))
                [inv_elim, dne, ie]

  le_antisymm <- chainLemma "a ≤ b → b ≤ a → a = b"
                            (\AB -> a ≤ b .=> b ≤ a .=> a .== b)
                            (\a b -> (a ≤ b .&& b ≤ a, [ a
                                                       , b ⨅ a
                                                       , a ⨅ b
                                                       , b :: SStroke
                                                       ]))
                            [commut2]

  le_refl <- lemma "a ≤ a" (\A -> a ≤ a) [idemp2]

  le_trans <- chainLemma "a ≤ b → b ≤ c → a ≤ c"
                         (\ABC -> a ≤ b .=> b ≤ c .=> a ≤ c)
                         (\a b c -> (a ≤ b .&& b ≤ c, [ a
                                                      , b ⨅ a
                                                      , (c ⨅ b) ⨅ a
                                                      , c ⨅ (b ⨅ a)
                                                      , c ⨅ a :: SStroke
                                                      ]))
                         [assoc2]

  pure BooleanAlgebraProof {
            le_refl          {- ∀ (a : α), a ≤ a                             -} = le_refl
          , le_trans         {- ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c         -} = error "TODO"
          , lt_iff_le_not_le {- (∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a)        -} = error "TODO"
          , le_antisymm      {- ∀ (a b : α), a ≤ b → b ≤ a → a = b           -} = error "TODO"
          , le_sup_left      {- ∀ (a b : α), a ≤ a ⊔ b                       -} = error "TODO"
          , le_sup_right     {- ∀ (a b : α), b ≤ a ⊔ b                       -} = error "TODO"
          , sup_le           {- ∀ (a b c : α), a ≤ c → b ≤ c → a ⊔ b ≤ c     -} = error "TODO"
          , inf_le_left      {- ∀ (a b : α), a ⊓ b ≤ a                       -} = error "TODO"
          , inf_le_right     {- ∀ (a b : α), a ⊓ b ≤ b                       -} = error "TODO"
          , le_inf           {- ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c     -} = error "TODO"
          , le_sup_inf       {- ∀ (x y z : α), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z -} = error "TODO"
          , inf_compl_le_bot {- ∀ (x : α), x ⊓ xᶜ ≤ ⊥                        -} = error "TODO"
          , top_le_sup_compl {- ∀ (x : α), ⊤ ≤ x ⊔ xᶜ                        -} = error "TODO"
          , le_top           {- ∀ (a : α), a ≤ ⊤                             -} = error "TODO"
          , bot_le           {- ∀ (a : α), ⊥ ≤ a                             -} = error "TODO"
          , sdiff_eq         {- (∀ (x y : α), x \ y = x ⊓ yᶜ)                -} = error "TODO"
          , himp_eq          {- (∀ (x y : α), x ⇨ y = y ⊔ xᶜ)                -} = error "TODO" i1 le_antisymm le_refl le_trans
       }

{-
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
