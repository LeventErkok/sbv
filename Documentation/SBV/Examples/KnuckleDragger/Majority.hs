-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Majority
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving Boyer-Moore's majority algorithm correct. We use the ideas in
-- Tobias Nipkow's proof (See https://www21.in.tum.de/~nipkow/pubs/ijsi11.pdf),
-- though the paper is sparse on details which we fill here. (See Section 5 of
-- the paper.)
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
              \ih xs k c m ->
                   [majority (replicate k c ++ xs) m]
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
                                , k .<= 0 ==> c
                                           -- Note that the assumption
                                           --
                                           --    majority (replicate k c ++ xs) m
                                           --
                                           -- evaluates to False in this case. Why? Well,
                                           -- @xs@ is null, and so is @replicate k c@, so
                                           -- we get @majority [] m@, which then leads
                                           -- to '0 .< 0', i.e., false. That is, the case
                                           -- combined implication leads to a contradiction
                                           -- Hence, we're justified in putting 'sFalse'
                                           -- here as the reason, since False implies everything.
                                           --
                                           -- In fact, we can even totally skip the @k .<= 0@ case
                                           -- as the SMT solver will figure that out on its own, but
                                           -- we're being explicit here.
                                           ?? sFalse
                                           =: m
                                           =: qed
                                ])
                         (\a as -> ite (a .== c)
                                       (cand c (k+1) as)
                                       (ite (k .== 0)
                                            (cand a 1     as)
                                            (cand c (k-1) as))
                                =: cases [ a .== c
                                           ==> cand c (k+1) as
                                            ?? ih `at` (Inst @"xs" as, Inst @"k" (k+1), Inst @"c" c, Inst @"m" m)
                                            ?? "c1"
                                            ?? sorry
                                            =: m
                                            =: qed
                                         , a ./= c .&& k .== 0
                                           ==> cand a 1 as
                                            ?? ih `at` (Inst @"xs" as, Inst @"k" (1 :: SInteger), Inst @"c" a, Inst @"m" m)
                                            ?? "c2"
                                            ?? sorry
                                            =: m
                                            =: qed
                                         , a ./= c .&& k ./= 0
                                           ==> cand c (k-1) as
                                            ?? ih `at` (Inst @"xs" as, Inst @"k" (k-1), Inst @"c" c, Inst @"m" m)
                                            ?? "c3"
                                            ?? sorry
                                            =: m
                                            =: qed
                                         ])

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
