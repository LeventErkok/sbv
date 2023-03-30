-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Rabbits
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A puzzle, attributed to Lewis Caroll:
--
--   - All rabbits, that are not greedy, are black
--   - No old rabbits are free from greediness
--   - Therefore: Some black rabbits are not old
--
-- What's implicit here is that there is a rabbit that must be not-greedy;
-- which we add to our constraints.
-----------------------------------------------------------------------------
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Rabbits where

import Data.SBV

-- | A universe of rabbits
data Rabbit

-- | Make rabbits symbolically available.
mkUninterpretedSort ''Rabbit

-- | Identify those rabbits that are greedy. Note that we leave the predicate uninterpreted.
greedy :: SRabbit -> SBool
greedy = uninterpret "greedy"

-- | Identify those rabbits that are black. Note that we leave the predicate uninterpreted.
black :: SRabbit -> SBool
black = uninterpret "black"

-- | Identify those rabbits that are old. Note that we leave the predicate uninterpreted.
old :: SRabbit -> SBool
old = uninterpret "old"

-- | Express the puzzle.
rabbits :: Predicate
rabbits = do -- All rabbits that are not greedy are black
             constrain $ \(Forall x) -> sNot (greedy x) .=> black  x

             -- No old rabbits are free from greediness
             constrain $ \(Forall x) -> old x .=> greedy x

             -- There is at least one non-greedy rabbit
             constrain $ \(Exists x) -> sNot (greedy x)

             -- Therefore, there must be a black rabbit that's not old:
             pure $ quantifiedBool $ \(Exists x) -> black x .&& sNot (old x)

-- | Prove the claim. We have:
--
-- >>> rabbitsAreOK
-- Q.E.D.
rabbitsAreOK :: IO ThmResult
rabbitsAreOK = prove rabbits
