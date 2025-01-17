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
-- logic), implies it is a boolean algebra.
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

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV.Tools.KnuckleDragger(runKD)
#endif

-- * The sheffer stroke

-- | The abstract type for the domain.
data Stroke
mkUninterpretedSort ''Stroke

-- | The sheffer stroke operator
(︱) :: SStroke -> SStroke -> SStroke
(︱) = uninterpret "︱"
infixl 7 ︱

-- | Negation in terms of ǀ
ﬧ :: SStroke -> SStroke
ﬧ x = x ︱x

-- | Helper datatype to collect sheffer-axioms in.
data ShefferAxioms = ShefferAxioms { sh1 :: Proof
                                   , sh2 :: Proof
                                   , sh3 :: Proof
                                   }

-- | Collection of sheffer-axioms
shefferAxioms :: KD ShefferAxioms
shefferAxioms = do
   sh1 <- axiom "Sheffer Stroke 1" $ \(Forall @"a" a) ->                                 ﬧ(ﬧ a) .== a
   sh2 <- axiom "Sheffer Stroke 2" $ \(Forall @"a" a) (Forall @"b" b) ->                 a ︱(b ︱ﬧ b) .== ﬧ a
   sh3 <- axiom "Sheffer Stroke 3" $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> ﬧ(a ︱(b ︱c)) .== (ﬧ b ︱a) ︱(ﬧ c ︱a)

   pure $ ShefferAxioms { sh1 = sh1, sh2 = sh2, sh3 = sh3 }

-- * Commmutativity

-- | Prove that the sheffer stroke is commutative. We have:
--
-- >>> runKD commutative
-- Axiom: Sheffer Strok  1                 Axiom.
-- Axiom: Sheffer Stroke 2                 Axiom.
-- Axiom: Sheffer Stroke 3                 Axiom.
-- Chain lemma: commutative
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q E.D.
--   Result:                               Q.E.D.
-- [Proven] commutativie
commutative :: KD Proof
commutative = do
   ShefferAxioms {sh1, sh3} <- shefferAxioms
   chainLemma "commutative"
              (\(Forall @"a" a) (Forall @"b" b) -> a ︱b .== b ︱a)
              (pure ())
              (\a b -> [ a ︱b
                       , ﬧ(ﬧ(a ︱b))
                       , ﬧ(ﬧ(a ︱ﬧ(ﬧ b)))
                       , ﬧ(ﬧ (ﬧ(ﬧ b) ︱ a))
                       , b ︱ a
                       ])
              [sh1, sh3]

-- * Bottom elements are the same

-- | Prove that @a ︱ﬧ a == b ︱ﬧ b@ for all elements, that is, bottom element is unique. We have:
--
-- >>> runKD all_bot
all_bot :: KD Proof
all_bot = do
  ShefferAxioms {sh1, sh2} <- shefferAxioms
  commut                   <- commutative

  chainLemma "all_bot"
             (\(Forall @"a" a) (Forall @"b" b) -> a ︱ﬧ a .== b ︱ﬧ b)
             (pure ())
             (\a b -> [ a ︱ﬧ a
                      , ﬧ ((a ︱ﬧ a) ︱(b ︱ﬧ b))
                      , ﬧ ((b ︱ﬧ b) ︱(a ︱ﬧ a))
                      , ﬧ (ﬧ (b ︱ﬧ b))
                      , b ︱ ﬧ b
                      ])
            [sh1, sh2, commut]
