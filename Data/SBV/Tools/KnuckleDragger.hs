-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KnuckleDragger
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A lightweight theorem proving like interface, built on top of SBV.
-- Inspired by and modeled after Philip Zucker's tool with the same
-- name, see <http://github.com/philzook58/knuckledragger>.
--
-- See the directory Documentation.SBV.Examples.KnuckleDragger for various examples.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger (
       -- * Propositions and their proofs
         Proposition, Proof

       -- * Adding axioms/definitions
       , axiom

       -- * Basic proofs
       , lemma, lemmaWith, theorem, theoremWith

       -- * Reasoning via calculation
       , calc, calcWith, calcThm, calcThmWith

       -- * Reasoning via regular induction
       , induct,  inductWith, inductThm, inductThmWith

       -- * Reasoning via strong induction
       , sInduct, sInductWith, sInductThm, sInductThmWith

       -- * Creating instances of proofs
       , at, Inst(..)

       -- * Faking proofs
       , sorry

       -- * Running KnuckleDragger proofs
       , KD, runKD, runKDWith, use

       -- * Starting a calculation proof
       , (|-), (⊢)

       -- * Sequence of calculation steps
       , (=:), (≡)

       -- * Supplying hints for a calculation step
       , (??), (⁇), hprf, hyp

       -- * Case splits
       , cases

       -- * Finishing up a calculational proof
       , qed
       ) where

import Data.SBV.Tools.KD.KnuckleDragger
