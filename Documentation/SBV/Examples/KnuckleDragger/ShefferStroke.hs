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

{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeAbstractions   #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.ShefferStroke where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | The abstract type for the domain.
data Stroke
mkUninterpretedSort ''Stroke

-- | The sheffer stroke.
ǀ :: SStroke -> SStroke -> SStroke
ǀ =  uninterpret "∣"

-- | Negation in terms of ǀ
ﬧ :: SStroke -> SStroke
ﬧ x = x `ǀ` x

-- | Axioms of the sheffer stroke.
shefferAxioms :: KD [Proof]
shefferAxioms = do sh1 <- axiom "sh1" $ \(Forall @"a" a)                                 -> ﬧ (ﬧ a) .== a
                   sh2 <- axiom "sh2" $ \(Forall @"a" a) (Forall @"b" b)                 -> a `ǀ` (b `ǀ` ﬧ b) .== ﬧ a
                   sh3 <- axiom "sh3" $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> ﬧ (a `ǀ` (b `ǀ` c)) .== (ﬧ b `ǀ` a) `ǀ` (ﬧ c `ǀ` a)
                   pure [sh1, sh2, sh3]

-- * Commmutativity

-- | Prove that the sheffer stroke is commutative. We have:
--
-- >>> commutative
-- Axiom: sh1                              Axiom.
-- Axiom: sh2                              Axiom.
-- Axiom: sh3                              Axiom.
-- Lemma: commutative                      Q.E.D.
-- [Proven] commutative
commutative :: IO Proof
commutative = runKD $ do
   shefferAxioms >>= lemma "commutative" (\(Forall @"a" a) (Forall @"b" b) -> a `ǀ` b .== b `ǀ` a)
