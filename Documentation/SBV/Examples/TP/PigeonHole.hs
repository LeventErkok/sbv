-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.PigeonHole
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves the pigeon-hole principle. If a list of integers sum to more than the length
-- of the list itself, then some cell must contain a value larger than @1@.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.PigeonHole where

import Prelude hiding (sum, length, elem, null)

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- | Overflow: Some value is greater than 1.
overflow :: SList Integer -> SBool
overflow = smtFunction "overflow" $ \xs -> ite (null xs) sFalse
                                             $ let (a, as) = uncons xs
                                               in a .> 1 .|| overflow as

-- | \(\sum xs > \lvert xs \rvert \Rightarrow \textrm{overflow}\, xs\)
--
-- >>> runTP pigeonHole
-- Inductive lemma: pigeonHole
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
--[Proven] pigeonHole :: Ɐxs ∷ [Integer] → Bool
pigeonHole :: TP (Proof (Forall "xs" [Integer] -> SBool))
pigeonHole = induct "pigeonHole"
                   (\(Forall xs) -> sum xs .> length xs .=> overflow xs) $
                   \ih (x, xs) -> [sum xs .> length xs]
                               |- overflow (x .: xs)
                               =: (x .> 1 .|| overflow xs)
                               ?? ih
                               =: sTrue
                               =: qed
