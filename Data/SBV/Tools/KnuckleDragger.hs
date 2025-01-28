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
       , lemma,   lemmaWith
       , theorem, theoremWith

       -- * Chain of reasoning
       , chainLemma,   chainLemmaWith
       , chainTheorem, chainTheoremWith

       -- * Induction
       , induct, inductAlt1, inductAlt2
       , inductiveLemma,   inductiveLemmaWith
       , inductiveTheorem, inductiveTheoremWith

       -- * Creating instances of proofs
       , apply

       -- * Faking proofs
       , sorry

       -- * Running KnuckleDragger proofs
       , KD, runKD, runKDWith, use
       ) where

import Data.SBV.Tools.KD.KnuckleDragger
