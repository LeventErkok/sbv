-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Reverse
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
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Reverse where

import Prelude hiding (head, tail, null, reverse, length, init, last, (++))
import Data.Proxy

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.Tools.KnuckleDragger

import qualified Data.SBV.Tools.KnuckleDragger.Lists as KDL

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Proxy
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
-- >>> correctness (Proxy @Integer)
-- Inductive lemma: reversePreservesLength @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revApp @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revApp @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: revSnoc @Integer                 Q.E.D.
-- Inductive lemma: revApp @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: reverseReverse @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): revCorrect @Integer
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
-- [Proven] revCorrect @Integer
correctness :: forall a. SymVal a => Proxy a -> IO Proof
correctness p = runKD $ do

  -- Import a few helpers from "Data.SBV.Tools.KnuckleDragger.List"
  revPreservesLength <- use $ KDL.reversePreservesLength p
  revApp             <- use $ KDL.revApp                 p
  revSnoc            <- use $ KDL.revSnoc                p
  reverseReverse     <- use $ KDL.reverseReverse         p

  sInductWith cvc5 (atProxy p "revCorrect")
    (\(Forall @"xs" (xs :: SList a)) -> rev xs .== reverse xs)
    (length @a) $
    \ih (xs :: SList a) ->
        [] |- rev xs
           =: split xs trivial
                    (\a as -> split as trivial
                                    (\_ _ -> head (rev as) .: rev (a .: rev (tail (rev as)))
                                          ?? ih `at` Inst @"xs" as
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
                                          ?? [ ih                 `at` Inst @"xs" (reverse w)
                                             , revPreservesLength `at` Inst @"xs" w
                                             ]
                                          =: b .: rev (a .: reverse (reverse w))
                                          ?? reverseReverse `at` Inst @"xs" w
                                          =: b .: rev (a .: w)
                                          ?? ih
                                          =: b .: reverse (a .: w)
                                          ?? "substitute"
                                          =: last as .: reverse (a .: init as)
                                          ?? revApp `at` (Inst @"xs" (init as), Inst @"ys" (singleton (last as)))
                                          =: reverse (a .: init as ++ singleton (last as))
                                          =: reverse (a .: as)
                                          =: reverse xs
                                          =: qed))
