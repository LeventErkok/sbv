-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Lists.CountOutAndTransfer
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Shows that COAT (Count-out-and-transfer) trick preserves order of cards.
-- From pg. 35 of <http://graphics8.nytimes.com/packages/pdf/crossword/Mulcahy_Mathematical_Card_Magic-Sample2.pdf>:
--
-- /Given a packet of n cards, COATing k cards refers to counting out that many from the top into a pile, thus reversing their order, and transferring those as a unit to the bottom./
--
-- We show that if you COAT 4 times where @k@ is at least @n/2@ for a deck of size @n@, then the deck remains in the same order.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Lists.CountOutAndTransfer where

import Prelude hiding (length, take, drop, reverse, (++))

import Data.SBV
import Data.SBV.List

-- | Count-out-and-transfer (COAT): Take @k@ cards from top, reverse it,
-- and put it at the bottom of a deck.
coat :: SymVal a => SInteger -> SList a -> SList a
coat k cards = drop k cards ++ reverse (take k cards)

-- | COAT 4 times.
fourCoat :: SymVal a => SInteger -> SList a -> SList a
fourCoat k = coat k . coat k . coat k . coat k

-- | A deck is simply a list of integers. Note that a regular deck will have
-- distinct cards, we do not impose this in our proof. That is, the
-- proof works regardless whether we put duplicates into the deck, which
-- generalizes the theorem.
type Deck = SList Integer

-- | Key property of COATing. If you take a deck of size @n@, and
-- COAT it 4 times, then the deck remains in the same order. The COAT
-- factor, @k@, must be greater than half the size of the deck size.
--
-- Note that the proof time increases significantly with @n@.
-- Here's a proof for deck size of 6, for all @k@ >= @3@.
--
-- >>> coatCheck 6
-- Q.E.D.
--
-- It's interesting to note that one can also express this theorem
-- by making @n@ symbolic as well. However, doing so definitely requires
-- an inductive proof, and the SMT-solver doesn't handle this case
-- out-of-the-box, running forever.
coatCheck :: Integer -> IO ThmResult
coatCheck n = prove $ do
     deck :: Deck <- free "deck"
     k            <- free "k"

     constrain $ length deck .== literal n
     constrain $ 2*k .>= literal n

     pure $ deck .== fourCoat k deck
