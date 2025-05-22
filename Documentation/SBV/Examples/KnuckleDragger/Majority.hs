-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Majority
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving Boyer-Moore's majority algorithm correct. We follow Tobias Nipkow's
-- proof in https://www21.in.tum.de/~nipkow/pubs/ijsi11.pdf closely. (See
-- Section 5 of the paper.)
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Majority where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding (null, length, (++), replicate)
import Data.SBV.List

-- * Choosing majority

-- | Helper function to count candidates.
cand :: SInteger -> SInteger -> SList Integer -> SInteger
cand = smtFunction "cand" $ \c k xs -> ite (null xs) c
                                           (let (a, as) = uncons xs
                                            in ite (a .== c)
                                                   (cand c (k+1) as)
                                                   (ite (k .== 0)
                                                        (cand a 1     as)
                                                        (cand c (k-1) as)))

-- | Boyer and Moore's linear time algorithm to find the majority element, if it exists.
-- The return value is arbitrary if no majority element exists.
maj :: SList Integer -> SInteger
maj = cand 0 0

-- | Is a given element the majority in a list?
majority :: SList Integer -> SInteger -> SBool
majority l m = length l `sEDiv` 2 .< count l m
  where count :: SList Integer -> SInteger -> SInteger
        count = smtFunction "count" $ \xs c -> ite (null xs) 0
                                                   (let (a, as) = uncons xs
                                                        cnt     = count as c
                                                    in ite (a .== c) (1 + cnt) cnt)

-- * Correctness proof

-- | Correctness of the majority algorithm.  We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

    -- Majority of a replicated element is that element
    majSame <- lemma "majSame"
                     (\(Forall @"k" k) (Forall @"c" c) -> k .> 0 .=> majority (replicate k c) c)
                     [sorry]

    -- Majority, if exists, is unique
    majUnique <- lemma "majUnique"
                       (\(Forall @"xs" xs) (Forall @"m1" m1) (Forall @"m2" m2) ->
                            majority xs m1 .&& majority xs m2 .=> m1 .== m2)
                       [sorry]

    -- We prove a generalized version
    helper <-
      sInductWith cvc5 "helper"
              (\(Forall @"xs" xs) (Forall @"k" k) (Forall @"c" c) (Forall @"m" m)
                    -> majority (replicate k c ++ xs) m .=> cand c k xs .== m)
              (\xs (_k :: SInteger) (_c :: SInteger) (_m :: SInteger) -> length @Integer xs) $
              \ih xs k c m -> [majority (replicate k c ++ xs) m]
                           |- cand c k xs
                           =: split xs
                                    (cases [ k .>  0 ==> c
                                                      ?? [ majSame   `at` (Inst @"k" k, Inst @"c" c)
                                                         , majUnique `at` ( Inst @"xs" (replicate k c)
                                                                          , Inst @"m1" c
                                                                          , Inst @"m2" m
                                                                          )
                                                         ]
                                                      =: m
                                                      =: qed
                                           -- NB. We don't need a k .<= 0 case. Why?
                                           -- Because the solver can deduce that the
                                           -- assumption would imply @majority [] m@ can never be true
                                           -- in that case, since we'd have 0 < 0. Cool.
                                           ])
                                    (\a as -> ite (a .== c)
                                                  (cand c (k+1) as)
                                                  (ite (k .== 0)
                                                       (cand a 1     as)
                                                       (cand c (k-1) as))
                                           ?? ih
                                           ?? "stuck"
                                           ?? sorry
                                           =: m
                                           =: qed)

    -- The theorem now follows simply from the helper
    calc "correctness"
         (\(Forall @"xs" xs) (Forall @"m" m) -> majority xs m .=> maj xs .== m) $
         \xs m -> [majority xs m] |- maj xs
                                  =: cand 0 0 xs
                                  ?? helper `at` ( Inst @"xs" xs
                                                 , Inst @"k" (0 :: SInteger)
                                                 , Inst @"c" (0 :: SInteger)
                                                 , Inst @"m" m
                                                 )
                                  =: m
                                  =: qed
