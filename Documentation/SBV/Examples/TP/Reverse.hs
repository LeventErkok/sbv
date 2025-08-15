-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Reverse
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Can we define the reverse function using no auxiliary functions, i.e., only
-- in terms of cons, head, tail, and itself (recursively)? This example
-- shows such a definition and proves that it is correct.
--
-- See Zohar Manna's 1974 "Mathematical Theory of Computation" book, where this
-- definition and its proof is presented as Example 5.36.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Reverse where

import Prelude hiding (head, tail, null, reverse, length, init, last, (++))

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.TP

import qualified Data.SBV.TP.List as TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.SBV.TP
#endif

-- * Reversing with no auxiliaries

-- | This definition of reverse uses no helper functions, other than the usual
-- head, tail, cons, and uncons to reverse a given list. Note that efficiency
-- is not our concern here, we call 'rev' itself three times in the body.
rev :: SymVal a => SList a -> SList a
rev = smtFunction "rev" $ \xs -> ite (null xs .|| null (tail xs)) xs
                                     (let (x, as)     = uncons xs
                                          (hras, tas) = uncons (rev as)
                                      in hras .: rev (x .: rev tas))

-- * Correctness proof

-- | Correctness the function 'rev'. We have:
--
-- >>> runTP $ correctness @Integer
-- Inductive lemma: revLen
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revApp
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revApp
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: revSnoc                          Q.E.D.
-- Inductive lemma: revApp
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revRev
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): revCorrect
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2 (2 way full case split)
--       Step: 1.2.1                       Q.E.D.
--       Step: 1.2.2.1                     Q.E.D.
--       Step: 1.2.2.2                     Q.E.D.
--       Step: 1.2.2.3                     Q.E.D.
--       Step: 1.2.2.4                     Q.E.D.
--       Step: 1.2.2.5 (simplify head)     Q.E.D.
--       Step: 1.2.2.6                     Q.E.D.
--       Step: 1.2.2.7 (simplify tail)     Q.E.D.
--       Step: 1.2.2.8                     Q.E.D.
--       Step: 1.2.2.9                     Q.E.D.
--       Step: 1.2.2.10                    Q.E.D.
--       Step: 1.2.2.11 (substitute)       Q.E.D.
--       Step: 1.2.2.12                    Q.E.D.
--       Step: 1.2.2.13                    Q.E.D.
--       Step: 1.2.2.14                    Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revCorrect :: Ɐxs ∷ [Integer] → Bool
correctness :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
correctness = do

  -- Quietly import a few helpers from "Data.SBV.TP.List"
  revLen  <- recall "revLen"  $ TP.revLen  @a
  revApp  <- recall "revApp"  $ TP.revApp  @a
  revSnoc <- recall "revSnoc" $ TP.revSnoc @a
  revRev  <- recall "revRev"  $ TP.revRev  @a

  sInductWith cvc5 "revCorrect"
    (\(Forall xs) -> rev xs .== reverse xs)
    length $
    \ih xs -> [] |- rev xs
                 =: split xs trivial
                          (\a as -> split as trivial
                                          (\_ _ -> head (rev as) .: rev (a .: rev (tail (rev as)))
                                                ?? ih `at` Inst @"xs" as
                                                =: head (reverse as) .: rev (a .: rev (tail (rev as)))
                                                ?? ih `at` Inst @"xs" as
                                                ?? "slow"
                                                =: head (reverse as) .: rev (a .: rev (tail (reverse as)))
                                                ?? ih `at` Inst @"xs" (tail (rev as))
                                                =: head (reverse as) .: rev (a .: rev (tail (reverse as)))
                                                ?? revSnoc `at` (Inst @"x" (last as), Inst @"xs" (init as))
                                                =: let w = init as
                                                       b = last as
                                                in head (b .: reverse w) .: rev (a .: rev (tail (reverse as)))
                                                ?? "simplify head"
                                                =: b .: rev (a .: rev (tail (reverse as)))
                                                ?? revSnoc `at` (Inst @"x" (last xs), Inst @"xs" (init as))
                                                =: b .: rev (a .: rev (tail (b .: reverse w)))
                                                ?? "simplify tail"
                                                =: b .: rev (a .: rev (reverse w))
                                                ?? ih     `at` Inst @"xs" (reverse w)
                                                ?? revLen `at` Inst @"xs" w
                                                =: b .: rev (a .: reverse (reverse w))
                                                ?? revRev `at` Inst @"xs" w
                                                =: b .: rev (a .: w)
                                                ?? ih
                                                =: b .: reverse (a .: w)
                                                ?? "substitute"
                                                =: last as .: reverse (a .: init as)
                                                ?? revApp `at` (Inst @"xs" (a .: init as), Inst @"ys" [last as])
                                                =: reverse (a .: init as ++ [last as])
                                                =: reverse (a .: as)
                                                =: reverse xs
                                                =: qed))

{- HLint ignore correctness "Use last"          -}
{- HLint ignore correctness "Redundant reverse" -}
