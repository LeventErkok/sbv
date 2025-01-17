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
n :: SStroke -> SStroke
n x = x ︱x

-- | Helper datatype to collect sheffer-axioms in.
data ShefferAxioms = ShefferAxioms { sh1 :: Proof
                                   , sh2 :: Proof
                                   , sh3 :: Proof
                                   }

-- | Collection of sheffer-axioms
shefferAxioms :: KD ShefferAxioms
shefferAxioms = do
   sh1 <- axiom "Sheffer Stroke 1" $ \(Forall @"a" a) ->                                 n(n a) .== a
   sh2 <- axiom "Sheffer Stroke 2" $ \(Forall @"a" a) (Forall @"b" b) ->                 a ︱(b ︱n b) .== n a
   sh3 <- axiom "Sheffer Stroke 3" $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> n(a ︱(b ︱c)) .== (n b ︱a) ︱(n c ︱a)

   pure $ ShefferAxioms { sh1 = sh1, sh2 = sh2, sh3 = sh3 }

-- * Commmutativity

-- | Prove that the sheffer stroke is commutative. We have:
--
-- >>> runKD commutative
-- Axiom: Sheffer Stroke 1                 Axiom.
-- Axiom: Sheffer Stroke 2                 Axiom.
-- Axiom: Sheffer Stroke 3                 Axiom.
-- Chain lemma: commutative
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] commutative
commutative :: KD Proof
commutative = do
   ShefferAxioms {sh1, sh3} <- shefferAxioms
   chainLemma "commutative"
              (\(Forall @"a" a) (Forall @"b" b) -> a ︱b .== b ︱a)
              (pure ())
              (\a b -> [ a ︱b
                       , n(n(a ︱b))
                       , n(n(a ︱n(n b)))
                       , n(n (n(n b) ︱ a))
                       , b ︱ a
                       ])
              [sh1, sh3]

-- * Bottom elements are the same

-- | Prove that @a ︱n a == b ︱n b@ for all elements, that is, bottom element is unique. We have:
--
-- >>> runKD all_bot
-- Axiom: Sheffer Stroke 1                 Axiom.
-- Axiom: Sheffer Stroke 2                 Axiom.
-- Axiom: Sheffer Stroke 3                 Axiom.
-- Chain lemma: commutative
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q.E.D.
--   Result:                               Q.E.D.
-- Chain lemma: all_bot
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] all_bot
all_bot :: KD Proof
all_bot = do
  ShefferAxioms {sh1, sh2} <- shefferAxioms
  commut                   <- commutative

  chainLemma "all_bot"
             (\(Forall @"a" a) (Forall @"b" b) -> a ︱n a .== b ︱n b)
             (pure ())
             (\a b -> [ a ︱n a
                      , n ((a ︱n a) ︱(b ︱n b))
                      , n ((b ︱n b) ︱(a ︱n a))
                      , n (n (b ︱n b))
                      , b ︱ n b
                      ])
            [sh1, sh2, commut]

-- * Infimum, supremum, bottom, and top

-- | Infimum: Greatest lower bound
inf :: SStroke -> SStroke -> SStroke
a `inf` b = n a ︱n b

-- | Supremum: Least upper bound
sup :: SStroke -> SStroke -> SStroke
a `sup` b = n (a ︱b)

-- | The unique bottom element
z :: SStroke
z = elt ︱n elt
 where elt = uninterpret "z"

-- | The unique top element
u :: SStroke
u = n z

-- | `inf` is commutative: @a `inf` b == b `inf` a@
--
-- We have:
--
-- >>> runKD infCommutes
-- Axiom: Sheffer Stroke 1                 Axiom.
-- Axiom: Sheffer Stroke 2                 Axiom.
-- Axiom: Sheffer Stroke 3                 Axiom.
-- Chain lemma: commutative
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: inf commutes                     Q.E.D.
-- [Proven] inf commutes
infCommutes :: KD Proof
infCommutes = do
  comm <- commutative

  lemma "inf commutes"
        (\(Forall @"a" a) (Forall @"b" b) -> a `inf` b .== b `inf` a)
        [comm]

-- | `sup` is commutative: @a `sup` b == b `sup` a@
--
-- We have:
--
-- >>> runKD supCommutes
-- Axiom: Sheffer Stroke 1                 Axiom.
-- Axiom: Sheffer Stroke 2                 Axiom.
-- Axiom: Sheffer Stroke 3                 Axiom.
-- Chain lemma: commutative
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: sup commutes                     Q.E.D.
-- [Proven] sup commutes
supCommutes :: KD Proof
supCommutes = do
  comm <- commutative

  lemma "sup commutes"
        (\(Forall @"a" a) (Forall @"b" b) -> a `inf` b .== b `inf` a)
        [comm]

-- | @a `sup` z == a@
--
-- >>> runKD supZ
-- Axiom: Sheffer Stroke 1                 Axiom.
-- Axiom: Sheffer Stroke 2                 Axiom.
-- Axiom: Sheffer Stroke 3                 Axiom.
-- Lemma: a `sup` z = a                    Q.E.D.
-- [Proven] a `sup` z = a
supZ :: KD Proof
supZ = do
  ShefferAxioms {sh1, sh2} <- shefferAxioms

  lemma "a `sup` z = a" (\(Forall @"a" a) -> a `sup` z .== a) [sh1, sh2]

-- | @a `inf` u == a@
--
-- >>> runKD infU
-- Axiom: Sheffer Stroke 1                 Axiom.
-- Axiom: Sheffer Stroke 2                 Axiom.
-- Axiom: Sheffer Stroke 3                 Axiom.
-- Lemma: a `inf` u = a                    Q.E.D.
-- [Proven] a `inf` u = a
infU :: KD Proof
infU = do
  ShefferAxioms {sh1, sh2} <- shefferAxioms

  lemma "a `inf` u = a" (\(Forall @"a" a) -> a `inf` u .== a) [sh1, sh2]
