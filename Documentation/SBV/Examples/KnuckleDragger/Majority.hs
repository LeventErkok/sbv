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
cand = smtFunction "cand" $ \c k l -> ite (null l) c
                                          (let (x, xs) = uncons l
                                           in ite (x .== c)
                                                  (cand c (k+1) xs)
                                                  (ite (k .== 0)
                                                       (cand x 1     xs)
                                                       (cand c (k-1) xs)))

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

    -- We prove a generalized version
    helper <-
      induct "helper"
             (\(Forall @"xs" xs) (Forall @"k" k) (Forall @"c" c) (Forall @"m" m)
                   -> majority (replicate k c ++ xs) m .=> cand c k xs .== m) $
             \ih x xs k c m -> [majority (replicate k c ++ (x .: xs)) m]
                            |- cand c k (x .: xs)
                            ?? ih
                            =: m
                            =: qed

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
