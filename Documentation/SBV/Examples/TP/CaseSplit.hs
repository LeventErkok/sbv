-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.CaseSplit
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Use TP to prove @2n^2 + n + 1@ is never divisible by @3@.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.CaseSplit where

import Data.SBV
import Data.SBV.Tools.TP

-- | Prove that @2n^2 + n + 1@ is not divisible by @3@.
--
-- We have:
--
-- >>> notDiv3
-- Lemma: notDiv3
--   Step: 1 (3 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] notDiv3
notDiv3 :: IO Proof
notDiv3 = runTP $ do

   let s n = 2 * n * n + n + 1

   -- Do a case-split for each possible outcome of @s n `sEMod` 3@. In each case
   -- we get the witness that is guaranteed to exist by the case condition, and rewrite
   -- @s n@ accordingly. Once this is done, z3 can figure out the rest by itself.
   calc "notDiv3"
        (\(Forall @"n" n) -> s n `sEMod` 3 ./= 0) $
        \n -> [] |- s n
                 =: cases [ n `sEMod` 3 .== 0 ==> s (0 + 3 * some "k" $ \k -> n .== 0 + 3 * k) =: qed
                          , n `sEMod` 3 .== 1 ==> s (1 + 3 * some "k" $ \k -> n .== 1 + 3 * k) =: qed
                          , n `sEMod` 3 .== 2 ==> s (2 + 3 * some "k" $ \k -> n .== 2 + 3 * k) =: qed
                          ]
