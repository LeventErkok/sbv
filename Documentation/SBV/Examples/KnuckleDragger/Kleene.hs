-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Kleene
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger layer, proving some Kleene algebra theorems.
--
-- Based on <http://www.philipzucker.com/bryzzowski_kat/>
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-matches #-}

module Documentation.SBV.Examples.KnuckleDragger.Kleene where

import Prelude hiding((<=))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | An uninterpreted sort, corresponding to the type of Kleene algebra strings.
data Kleene
mkUninterpretedSort ''Kleene

-- | Star operator over kleene algebras. We're leaving this uninterpreted.
star :: SKleene -> SKleene
star = uninterpret "star"

-- | The 'Num' instance for Kleene makes it easy to write regular expressions
-- in the more familiar form.
instance Num SKleene where
  (+) = uninterpret "par"
  (*) = uninterpret "seq"

  abs    = error "SKleene: not defined: abs"
  signum = error "SKleene: not defined: signum"
  negate = error "SKleene: not defined: signum"

  fromInteger 0 = uninterpret "zero"
  fromInteger 1 = uninterpret "one"
  fromInteger n = error $ "SKleene: not defined: fromInteger " ++ show n

-- | The set of strings matched by one regular expression is a subset of the second,
-- if adding it to the second doesn't change the second set.
(<=) :: SKleene -> SKleene -> SBool
x <= y = x + y .== y

-- | A sequence of Kleene algebra proofs. See <http://www.cs.cornell.edu/~kozen/Papers/ka.pdf>
--
-- We have:
--
-- >>> example
-- Axiom: par_assoc                               Admitted.
-- Axiom: par_comm                                Admitted.
-- Axiom: par_idem                                Admitted.
-- Axiom: par_zero                                Admitted.
-- Axiom: seq_assoc                               Admitted.
-- Axiom: seq_zero                                Admitted.
-- Axiom: seq_one                                 Admitted.
-- Axiom: rdistrib                                Admitted.
-- Axiom: ldistrib                                Admitted.
-- Axiom: unfold                                  Admitted.
-- Axiom: least_fix                               Admitted.
-- Lemma: par_lzero                               Q.E.D.
-- Lemma: par_monotone                            Q.E.D.
-- Lemma: seq_monotone                            Q.E.D.
-- Chain: star_star_1
--   Lemma: star_star_1.1                         Q.E.D.
--   Lemma: star_star_1.2                         Q.E.D.
--   Lemma: star_star_1.3                         Q.E.D.
--   Lemma: star_star_1.4                         Q.E.D.
-- Lemma: star_star_1                             Q.E.D.
-- Lemma: subset_eq                               Q.E.D.
-- Lemma: star_star_2_2                           Q.E.D.
-- Lemma: star_star_2_3                           Q.E.D.
-- Lemma: star_star_2_1                           Q.E.D.
-- Lemma: star_star_2                             Q.E.D.
example :: IO ()
example = do

  -- Kozen axioms
  par_assoc <- axiom "par_assoc" $ \(Forall (x :: SKleene)) (Forall y) (Forall z) -> x + (y + z) .== (x + y) + z
  par_comm  <- axiom "par_comm"  $ \(Forall (x :: SKleene)) (Forall y)            -> x + y       .== y + x
  par_idem  <- axiom "par_idem"  $ \(Forall (x :: SKleene))                       -> x + x       .== x
  par_zero  <- axiom "par_zero"  $ \(Forall (x :: SKleene))                       -> x + 0       .== x

  seq_assoc <- axiom "seq_assoc" $ \(Forall (x :: SKleene)) (Forall y) (Forall z) -> x * (y * z) .== (x * y) * z
  seq_zero  <- axiom "seq_zero"  $ \(Forall (x :: SKleene))                       -> x * 0       .== 0
  seq_one   <- axiom "seq_one"   $ \(Forall (x :: SKleene))                       -> x * 1       .== x

  rdistrib  <- axiom "rdistrib"  $ \(Forall (x :: SKleene)) (Forall y) (Forall z) -> x * (y + z) .== x * y + x * z
  ldistrib  <- axiom "ldistrib"  $ \(Forall (x :: SKleene)) (Forall y) (Forall z) -> (y + z) * x .== y * x + z * x

  unfold    <- axiom "unfold"    $ \(Forall e) -> star e .== 1 + e * star e

  least_fix <- axiom "least_fix" $ \(Forall x) (Forall e) (Forall f) -> ((f + e * x) <= x) .=> ((star e * f) <= x)

  -- Collect the basic axioms in a list for easy reference
  let kleene = [ par_assoc,  par_comm, par_idem, par_zero
               , seq_assoc,  seq_zero, seq_one
               , ldistrib,   rdistrib
               , unfold
               , least_fix
               ]

  -- Various proofs:
  par_lzero    <- lemma "par_lzero" (\(Forall (x :: SKleene)) -> 0 + x .== x) kleene
  par_monotone <- lemma "par_monotone" (\(Forall (x :: SKleene)) (Forall y) (Forall z) -> x <= y .=> ((x + z) <= (y + z))) kleene
  seq_monotone <- lemma "seq_monotone" (\(Forall (x :: SKleene)) (Forall y) (Forall z) -> x <= y .=> ((x * z) <= (y * z))) kleene

  -- This one requires a chain of reasoning: x* x* == x*
  star_star_1  <- chainLemma "star_star_1" (\(Forall (x :: SKleene)) -> star x * star x .== star x)
                                           (\x -> [ star x * star x
                                                  , (1 + x * star x) * (1 + x * star x)
                                                  , (1 + 1) + (x * star x + x * star x)
                                                  , 1 + x * star x
                                                  , star x
                                                  ])
                                           kleene

  subset_eq   <- lemma "subset_eq" (\(Forall x) (Forall y) -> (x .== y) .== (x <= y .&& y <= x)) kleene

  -- Prove: x** = x*
  star_star_2 <- do _1 <- lemma "star_star_2_2" (\(Forall x) -> ((star x * star x + 1) <= star x) .=> star (star x) <= star x) kleene
                    _2 <- lemma "star_star_2_3" (\(Forall x) -> star (star x) <= star x)                                             (kleene ++ [_1])
                    _3 <- lemma "star_star_2_1" (\(Forall x) -> star x        <= star (star x))                                      kleene

                    lemma "star_star_2" (\(Forall (x :: SKleene)) -> star (star x) .== star x) [subset_eq, _2, _3]

  pure ()