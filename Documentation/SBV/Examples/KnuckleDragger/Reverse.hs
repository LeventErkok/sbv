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

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Reverse where

import Prelude hiding (head, tail, null, reverse, length, init, last, (++))

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.Tools.KnuckleDragger

-- * Reversing with no auxiliaries

-- | This definition of reverse uses no helper functions, other than the usual
-- head, tail, cons, and uncons to reverse a given list. Note that efficiency
-- is not our concern here, we call 'rev' itself three times in the body.
rev :: SList Integer -> SList Integer
rev = smtFunction "rev" $ \xs -> ite (null xs .|| null (tail xs)) xs
                                     (let (x, as)     = uncons xs
                                          (hras, tas) = uncons (rev as)
                                      in hras .: rev (x .: rev tas))

-- * Correctness proof

-- | Correctness the function 'rev'. We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

  consRev <- lemma "consRev"
                   (\(Forall @"xs" xs) (Forall @"l" (l :: SInteger)) -> l .: reverse xs .== reverse (xs ++ singleton l))
                   [sorry]

  -- Reverse: preserves length
  revPreserveLength <- lemma "revPreserveLength"
                             (\(Forall @"xs" (xs :: SList Integer)) -> length (reverse xs) .== length xs)
                             [sorry]

  -- Reverse: double reverse is identity
  revRev <- lemma "revRev" (\(Forall @"xs" (xs :: SList Integer)) -> reverse (reverse xs) .== xs) [sorry]

  sInductWith cvc5 "revCorrect"
    (\(Forall @"xs" xs) -> rev xs .== reverse xs)
    (length @Integer) $
    \ih xs -> []
           |- rev xs
           =: split xs trivial
                    (\a as -> split as trivial
                                    (\_ _ -> head (rev as) .: rev (a .: rev (tail (rev as)))
                                          ?? ih `at` Inst @"xs" as
                                          =: head (reverse as) .: rev (a .: rev (tail (rev as)))
                                          ?? ih `at` Inst @"xs" as
                                          =: head (reverse as) .: rev (a .: rev (tail (reverse as)))
                                          ?? ih `at` Inst @"xs" (tail (rev as))
                                          =: head (reverse as) .: rev (a .: rev (tail (reverse as)))
                                          ?? consRev `at` (Inst @"xs" (init as), Inst @"l" (last as))
                                          =: let w = init as
                                                 b = last as
                                          in head (b .: reverse w) .: rev (a .: rev (tail (reverse as)))
                                          ?? "simplify head"
                                          =: b .: rev (a .: rev (tail (reverse as)))
                                          ?? consRev `at` (Inst @"xs" (init as), Inst @"l" (last as))
                                          =: b .: rev (a .: rev (tail (b .: reverse w)))
                                          ?? "simplify tail"
                                          =: b .: rev (a .: rev (reverse w))
                                          ?? [ hprf $ ih `at` Inst @"xs" (reverse w)
                                             , hprf $ revPreserveLength `at` Inst @"xs" w
                                             , hasm $ length w .< length as
                                             ]
                                          =: b .: rev (a .: reverse (reverse w))
                                          ?? revRev `at` Inst @"xs" w
                                          =: b .: rev (a .: w)
                                          ?? ih
                                          =: b .: reverse (a .: w)
                                          ?? "substitute"
                                          =: last as .: reverse (a .: init as)
                                          ?? consRev `at` (Inst @"xs" (a .: init as), Inst @"l" (last as))
                                          =: reverse (a .: init as ++ singleton (last as))
                                          =: reverse (a .: as)
                                          =: reverse xs
                                          =: qed))
