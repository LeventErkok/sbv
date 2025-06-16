-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.TP
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A lightweight theorem proving like interface, built on top of SBV.
-- Originally inspired by Philip Zucker's tool KnuckleDragger
-- see <http://github.com/philzook58/knuckledragger>, though SBV's
-- version is different in its scope and design significantly.
--
-- See the directory Documentation.SBV.Examples.TP for various examples.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP (
       -- * Propositions and their proofs
         Proposition, Proof, proofOf, assumptionFromProof

       -- * Getting the proof tree
       , rootOfTrust, RootOfTrust(..), ProofTree(..), showProofTree, showProofTreeHTML

       -- * Adding axioms/definitions
       , axiom

       -- * Basic proofs
       , lemma, lemmaWith, theorem, theoremWith

       -- * Reasoning via calculation
       , calc, calcWith, calcThm, calcThmWith

       -- * Reasoning via regular induction
       , induct,  inductWith, inductThm, inductThmWith

       -- * Reasoning via measure-based strong induction
       , sInduct, sInductWith, sInductThm, sInductThmWith, Measure(..)

       -- * Creating instances of proofs
       , at, Inst(..)

       -- * Faking proofs
       , sorry

       -- * Running TP proofs
       , TP, runTP, runTPWith, tpQuiet, tpRibbon, tpStats, tpCache

       -- * Starting a calculation proof
       , (|-), (⊢)

       -- * Sequence of calculation steps
       , (=:), (≡)

       -- * Supplying hints for a calculation step
       , (??), (∵)

       -- * Case splits
       , split, split2, cases, (⟹), (==>)

       -- * Finishing up a calculational proof
       , qed, trivial, contradiction

       -- * Helpers
       , atProxy
       ) where

import Data.SBV.TP.TP
