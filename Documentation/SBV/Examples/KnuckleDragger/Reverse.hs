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
-- We follow the proof given in Zohar Manna's 1974 "Mathematical Theory of Computation" book
-- fairly closely, where this definition and its proof is presented in Example 5.36.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Reverse where

import Prelude hiding (head, tail, null, reverse)

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.Tools.KnuckleDragger

-- * Reversing with no auxiliaries

-- | This definition of reverse uses no helper functions, other than the usual
-- head, tail, and cons to reverse a given list. Note that efficiency is not our
-- concern here.
rev :: SList Integer -> SList Integer
rev = smtFunction "rev" $ \l -> ite (null l .|| null (tail l)) l
                                    (let (h, t)     = uncons l
                                         (hrt, trt) = uncons (rev t)
                                     in hrt .: rev (h .: rev trt))

-- * Correctness proof

-- | Correctness the function 'rev'. We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $

  induct "revCorrect"
         (\(Forall @"xs" xs) -> rev xs .== reverse xs) $
         \ih h t -> []
                 |- rev (h .: t)
                 =: split t ((h .: t) =: qed)
                            (\y ys -> rev (h .: y .: ys)
                                   ?? "unfold"
                                   =: let (hrt, trt) = uncons (rev (y .: ys))
                                   in hrt .: rev (h .: rev trt)
                                   ?? ih
                                   =: reverse (h .: y .: ys)
                                   =: qed)
