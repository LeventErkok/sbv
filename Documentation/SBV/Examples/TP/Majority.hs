-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Majority
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving Boyer-Moore's majority algorithm correct. We follow the ACL2 proof
-- closely, which you can find at <https://github.com/acl2/acl2/blob/master/books/demos/majority-vote.lisp>.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Majority where

import Prelude hiding (null, length)

import Data.SBV
import Data.SBV.List

import Data.Proxy

import Data.SBV.TP
import qualified Data.SBV.TP.List as TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Proxy
#endif

-- * Calculating majority

-- | Given a list, calculate the majority element using Boyer-Moore's algorithm.
-- Note that the algorithm returns the majority if it exists. If there is no
-- majority element, then the result is irrelevant.
majority :: SymVal a => SBV a -> SInteger -> SList a -> SBV a
majority = smtFunction "majority"
                    $ \c i lst ->  ite (null lst) c
                                       (let (x, xs) = uncons lst
                                        in ite (i .== 0)
                                                (majority x 1 xs)
                                                (majority c (i + ite (c .== x) 1 (-1)) xs))

-- | We can now define mjrty, which simply feeds the majority function with an arbitrary element of the domain.
-- By the definition of 'majority' above, this arbitrary element will be returned if the given list is empty.
-- Otherwise, majority will be returned if it exists, and an element of the list otherwise.
mjrty :: SymVal a => SList a -> SBV a
mjrty = majority (some "arb" (const sTrue)) 0

-- | The function @how-many@ in the paper is already defined in SBV as 'TP.count'. Let's give it a name:
howMany :: SymVal a => SBV a -> SList a -> SInteger
howMany = TP.count

-- * Correctness

-- | The generalized majority theorem. This comment is taken more or less
-- directly from J's proof, cast in SBV terms:
--
-- This is the generalized theorem that explains how majority works on any @c@ and
-- @i@ instead of just on the initial @c@ and @i=0@.
--
-- The way to imagine @majority c i xs@ is that we started with
-- a bigger @xs'@ that contains @i@ occurrences of c followed by @xs@. That is,
-- @xs' = replicate i c ++ xs@.  We know that @majority c 0 xs'@ finds
-- the majority in @xs'@ if there is one.
--
-- So the generalized theorem supposes that @e@ occurs a majority of times in @xs'@.
-- We can say that in terms of @c@, @i@, and @xs@: the number of times @e@ occurs in @xs@
-- plus @i@ (if @e@ is @c@) is greater than half of the length of @xs@ plus @i@.
--
-- The conclusion states that @majority c i x@ is @e@. We have:
--
-- >>> correctness  (Proxy @Integer)
-- Inductive lemma: majorityGeneral @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                   Q.E.D.
--       Step: 1.2.2.1.2                   Q.E.D.
--       Step: 1.2.2.2.1                   Q.E.D.
--       Step: 1.2.2.2.2                   Q.E.D.
--       Step: 1.2.2.Completeness          Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: majority @Integer                Q.E.D.
-- Lemma: ifExistsFound @Integer           Q.E.D.
-- Lemma: ifNoMajority @Integer            Q.E.D.
-- Lemma: uniqueness @Integer
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- ([Proven] majority @Integer,[Proven] ifExistsFound @Integer,[Proven] ifNoMajority @Integer,[Proven] uniqueness @Integer)
correctness :: forall a. SymVal a => Proxy a
            -> IO ( Proof (Forall "c" a -> Forall "xs" [a] -> SBool)                    -- If majority exists, the calculated value is majority
                  , Proof (Forall "c" a -> Forall "xs" [a] -> SBool)                    -- If majority exists, it is found
                  , Proof (Forall "c" a -> Forall "xs" [a] -> SBool)                    -- If returned value isn't majority, then no majority exists
                  , Proof (Forall "m1" a -> Forall "m2" a  -> Forall "xs" [a] -> SBool) -- Uniqueness: If there are two majorities, they're the same
                  )
correctness _ = runTP $ do

  -- Helper definition
  let isMajority :: SBV a -> SList a -> SBool
      isMajority e xs = length xs `sEDiv` 2 .< TP.count e xs

  -- First prove the generalized majority theorem
  majorityGeneral <-
     induct "majorityGeneral"
            (\(Forall @"xs" xs) (Forall @"i" i) (Forall @"e" (e :: SBV a)) (Forall @"c" c)
                  -> i .>= 0 .&& (length xs + i) `sEDiv` 2 .< ite (e .== c) i 0 + TP.count e xs .=> majority c i xs .== e) $
            \ih (x, xs) i e c ->
                   [i .>= 0, (length (x .: xs) + i) `sEDiv` 2 .< ite (e .== c) i 0 + TP.count e (x .: xs)]
                |- majority c i (x .: xs)
                =: cases [ i .== 0 ==> majority x 1 xs
                                    ?? ih `at` (Inst @"i" 1, Inst @"e" e, Inst @"c" x)
                                    =: e
                                    =: qed
                         , i .>  0 ==> majority c (i + ite (c .== x) 1 (-1)) xs
                                    =: cases [ c .== x ==> majority c (i + 1) xs
                                                        ?? ih `at` (Inst @"i" (i+1), Inst @"e" e, Inst @"c" c)
                                                        =: e
                                                        =: qed
                                             , c ./= x ==> majority c (i - 1) xs
                                                        ?? ih `at` (Inst @"i" (i-1), Inst @"e" e, Inst @"c" c)
                                                        =: e
                                                        =: qed
                                             ]
                         ]

  -- We can now prove the main theorem, by instantiating the general version.
  correct <- lemma "majority"
                   (\(Forall @"c" c) (Forall @"xs" xs) -> isMajority c xs .=> mjrty xs .== c)
                   [proofOf majorityGeneral]

  -- Corollary: If there is a majority element, then what we return is a majority element:
  ifExistsFound <- lemma "ifExistsFound"
                        (\(Forall @"c" c) (Forall @"xs" xs) -> isMajority c xs .=> isMajority (mjrty xs) xs)
                        [proofOf correct]

  -- Contrapositive to the above: If the returned value is not majority, then there is no majority:
  ifNoMajority <- lemma "ifNoMajority"
                        (\(Forall c) (Forall xs) -> sNot (isMajority (mjrty xs) xs) .=> sNot (isMajority c xs))
                        [proofOf ifExistsFound]

  -- Let's also prove majority is unique, while we're at it, even though it is not essential for our main argument.
  unique <- calc "uniqueness"
                 (\(Forall m1) (Forall m2) (Forall xs) -> isMajority m1 xs .&& isMajority m2 xs .=> m1 .== m2) $
                 \m1 m2 xs -> [isMajority m1 xs, isMajority m2 xs]
                           |- m1
                           ?? correct `at` (Inst @"c" m1, Inst @"xs" xs)
                           ?? correct `at` (Inst @"c" m2, Inst @"xs" xs)
                           =: m2
                           =: qed

  pure (correct, ifExistsFound, ifNoMajority, unique)
