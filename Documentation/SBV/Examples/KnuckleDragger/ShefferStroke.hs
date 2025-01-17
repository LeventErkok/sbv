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
   sh1 <- axiom "sh1" $ \(Forall @"a" a) ->                                 ﬧ(ﬧ a) .== a
   sh2 <- axiom "sh2" $ \(Forall @"a" a) (Forall @"b" b) ->                 a ︱(b ︱ﬧ b) .== ﬧ a
   sh3 <- axiom "sh3" $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> ﬧ(a ︱(b ︱c)) .== (ﬧ b ︱a) ︱(ﬧ c ︱a)

   pure $ ShefferAxioms { sh1 = sh1, sh2 = sh2, sh3 = sh3 }

-- * Commmutativity

-- | Prove that the sheffer stroke is commutative. We have:
--
-- >>> commutative
-- Axiom: sh1                              Axiom.
-- Axiom: sh2                              Axiom.
-- Axiom: sh3                              Axiom.
-- Chain lemma: commutative
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] commutative
commutative :: IO Proof
commutative = runKD $ do
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
