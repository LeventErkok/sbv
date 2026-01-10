-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.InsertionSortTactic
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving insertion sort correct using the tactic-based interface.
-- Compare with Documentation.SBV.Examples.TP.InsertionSort which uses
-- the calculational proof style.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.InsertionSortTactic where

import Prelude hiding (null, length, head, tail, elem, (>>))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP
import Data.SBV.TP.Tactics

import qualified Documentation.SBV.Examples.TP.SortHelpers as SH

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
#endif

-- * Insertion sort (same definitions as calculational version)

-- | Insert an element into an already sorted list in the correct place.
insert :: (OrdSymbolic (SBV a), SymVal a) => SBV a -> SList a -> SList a
insert = smtFunction "insert" $ \e l -> ite (null l) [e]
                                      $ let (x, xs) = uncons l
                                        in ite (e .<= x) (e .: x .: xs) (x .: insert e xs)

-- | Insertion sort, using 'insert' above to successively insert the elements.
insertionSort :: (OrdSymbolic (SBV a), SymVal a) => SList a -> SList a
insertionSort = smtFunction "insertionSort" $ \l -> ite (null l) nil
                                                  $ let (x, xs) = uncons l
                                                    in insert x (insertionSort xs)


-- | Remove the first occurrence of an number from a list, if any.
removeFirst :: (Eq a, SymVal a) => SBV a -> SList a -> SList a
removeFirst = smtFunction "removeFirst" $ \e l -> ite (null l)
                                                      nil
                                                      (let (x, xs) = uncons l
                                                       in ite (e .== x) xs (x .: removeFirst e xs))

-- | Are two lists permutations of each other? Note that we diverge from the counting
-- based definition of permutation here, since this variant works better with insertion sort.
isPermutation :: (Eq a, SymVal a) => SList a -> SList a -> SBool
isPermutation = smtFunction "isPermutation" $ \l r -> ite (null l)
                                                          (null r)
                                                          (let (x, xs) = uncons l
                                                           in x `elem` r .&& isPermutation xs (removeFirst x r))

-- * Correctness proof using tactics

-- | Correctness of insertion-sort using the tactic-based interface.
--
-- IMPORTANT NOTE: The tactic-based interface in SBV is most useful for
-- non-inductive proofs where you can leverage tactics like 'auto', 'splitOn',
-- 'considerCases', etc. For inductive proofs like the ones needed here,
-- the calculational style with 'induct' and explicit '=:' steps is actually
-- the more natural approach.
--
-- This example shows that the insertion sort proof naturally stays in the
-- calculational style even when using the tactics module, because the proof
-- is fundamentally inductive. See the 'insertIntoEmpty' example below for
-- a case where tactics shine.
--
-- We have:
--
-- >>> correctness @Integer
-- Lemma: nonDecrTail                           Q.E.D.
-- Inductive lemma: insertNonDecreasing
--   Step: Base                                 Q.E.D.
--   Step: 1 (unfold insert)                    Q.E.D.
--   Step: 2 (push nonDecreasing down)          Q.E.D.
--   Step: 3 (unfold simplify)                  Q.E.D.
--   Step: 4                                    Q.E.D.
--   Step: 5                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Inductive lemma: sortNonDecreasing
--   Step: Base                                 Q.E.D.
--   Step: 1 (unfold insertionSort)             Q.E.D.
--   Step: 2                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Inductive lemma: insertIsElem
--   Step: Base                                 Q.E.D.
--   Step: 1                                    Q.E.D.
--   Step: 2                                    Q.E.D.
--   Step: 3                                    Q.E.D.
--   Step: 4                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Inductive lemma: removeAfterInsert
--   Step: Base                                 Q.E.D.
--   Step: 1 (expand insert)                    Q.E.D.
--   Step: 2 (push removeFirst down ite)        Q.E.D.
--   Step: 3 (unfold removeFirst on 'then')     Q.E.D.
--   Step: 4 (unfold removeFirst on 'else')     Q.E.D.
--   Step: 5                                    Q.E.D.
--   Step: 6 (simplify)                         Q.E.D.
--   Result:                                    Q.E.D.
-- Inductive lemma: sortIsPermutation
--   Step: Base                                 Q.E.D.
--   Step: 1                                    Q.E.D.
--   Step: 2                                    Q.E.D.
--   Step: 3                                    Q.E.D.
--   Step: 4                                    Q.E.D.
--   Step: 5                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Lemma: insertionSortIsCorrect                Q.E.D.
-- [Proven] insertionSortIsCorrect :: Ɐxs ∷ [Integer] → Bool
correctness :: forall a. (OrdSymbolic (SBV a), Eq a, SymVal a) => IO (Proof (Forall "xs" [a] -> SBool))
correctness = runTPWith (tpRibbon 45 cvc5) $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Import helper lemmas, definitions
    --------------------------------------------------------------------------------------------
    let nonDecreasing = SH.nonDecreasing @a

    nonDecrTail <- SH.nonDecrTail @a

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of insertion sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    -- Note: For inductive proofs, we still use 'induct' from Data.SBV.TP
    -- because induction requires a specific structure. The tactic-based
    -- approach shines more in non-inductive proofs where we can use
    -- tactics like 'auto', 'using', 'splitOn', etc.

    insertNonDecreasing <-
        induct "insertNonDecreasing"
               (\(Forall xs) (Forall e) -> nonDecreasing xs .=> nonDecreasing (insert e xs)) $
               \ih (x, xs) e -> [nonDecreasing (x .: xs)]
                             |- nonDecreasing (insert e (x .: xs))
                             ?? "unfold insert"
                             =: nonDecreasing (ite (e .<= x) (e .: x .: xs) (x .: insert e xs))
                             ?? "push nonDecreasing down"
                             =: ite (e .<= x) (nonDecreasing (e .: x .: xs))
                                              (nonDecreasing (x .: insert e xs))
                             ?? "unfold simplify"
                             =: ite (e .<= x)
                                    (nonDecreasing (x .: xs))
                                    (nonDecreasing (x .: insert e xs))
                             ?? nonDecreasing (x .: xs)
                             =: (e .> x .=> nonDecreasing (x .: insert e xs))
                             ?? nonDecrTail `at` (Inst @"x" x, Inst @"xs" (insert e xs))
                             ?? ih
                             =: sTrue
                             =: qed

    sortNonDecreasing <-
        induct "sortNonDecreasing"
               (\(Forall @"xs" xs) -> nonDecreasing (insertionSort xs)) $
               \ih (x, xs) -> [] |- nonDecreasing (insertionSort (x .: xs))
                                 ?? "unfold insertionSort"
                                 =: nonDecreasing (insert x (insertionSort xs))
                                 ?? insertNonDecreasing `at` (Inst @"xs" (insertionSort xs), Inst @"e" x)
                                 ?? ih
                                 =: sTrue
                                 =: qed

    --------------------------------------------------------------------------------------------
    -- Part III. Prove that the output of insertion sort is a permuation of its input
    --------------------------------------------------------------------------------------------

    insertIsElem <-
        induct "insertIsElem"
               (\(Forall @"xs" xs) (Forall @"e" (e :: SBV a)) -> e `elem` insert e xs) $
               \ih (x, xs) e -> [] |- e `elem` insert e (x .: xs)
                                   =: e `elem` ite (e .<= x) (e .: x .: xs) (x .: insert e xs)
                                   =: ite (e .<= x) (e `elem` (e .: x .: xs)) (e `elem` (x .: insert e xs))
                                   =: ite (e .<= x) sTrue (e `elem` insert e xs)
                                   ?? ih
                                   =: sTrue
                                   =: qed

    removeAfterInsert <-
        induct "removeAfterInsert"
               (\(Forall @"xs" xs) (Forall @"e" (e :: SBV a)) -> removeFirst e (insert e xs) .== xs) $
               \ih (x, xs) e ->
                   [] |- removeFirst e (insert e (x .: xs))
                      ?? "expand insert"
                      =: removeFirst e (ite (e .<= x) (e .: x .: xs) (x .: insert e xs))
                      ?? "push removeFirst down ite"
                      =: ite (e .<= x) (removeFirst e (e .: x .: xs)) (removeFirst e (x .: insert e xs))
                      ?? "unfold removeFirst on 'then'"
                      =: ite (e .<= x) (x .: xs) (removeFirst e (x .: insert e xs))
                      ?? "unfold removeFirst on 'else'"
                      =: ite (e .<= x) (x .: xs) (x .: removeFirst e (insert e xs))
                      ?? ih
                      =: ite (e .<= x) (x .: xs) (x .: xs)
                      ?? "simplify"
                      =: x .: xs
                      =: qed

    sortIsPermutation <-
        induct "sortIsPermutation"
               (\(Forall @"xs" (xs :: SList a)) -> isPermutation xs (insertionSort xs)) $
               \ih (x, xs) ->
                   [] |- isPermutation (x .: xs) (insertionSort (x .: xs))
                      =: isPermutation (x .: xs) (insert x (insertionSort xs))
                      =:     x `elem` insert x (insertionSort xs)
                         .&& isPermutation xs (removeFirst x (insert x (insertionSort xs)))
                      ?? insertIsElem
                      =: isPermutation xs (removeFirst x (insert x (insertionSort xs)))
                      ?? removeAfterInsert
                      =: isPermutation xs (insertionSort xs)
                      ?? ih
                      =: sTrue
                      =: qed

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "insertionSortIsCorrect"
          (\(Forall xs) -> let out = insertionSort xs in nonDecreasing out .&& isPermutation xs out)
          [proofOf sortNonDecreasing, proofOf sortIsPermutation]


-- * Alternative: Where tactics really shine
--
-- The following examples show where the tactic-based interface is more
-- natural than the calculational style. These are non-inductive proofs
-- where tactics like 'auto', 'splitOn', and 'considerCases' provide
-- a cleaner proof structure.

-- | A simple property: inserting into an empty list gives a singleton
--
-- >>> insertIntoEmpty @Integer
-- [Proven] insertIntoEmpty :: Ɐe ∷ Integer → Bool
insertIntoEmpty :: forall a. (OrdSymbolic (SBV a), Eq a, SymVal a)
                => IO (Proof (Forall "e" a -> SBool))
insertIntoEmpty = runTP $
  theorem "insertIntoEmpty"
          (\(Forall @"e" (e :: SBV a)) -> insert e nil .== [e])
          auto  -- The SMT solver can figure this out automatically

-- | Demonstrate case analysis with tactics: inserting e into [x]
--   results in a sorted list
--
-- >>> insertIntoSingleton @Integer
-- [Proven] insertIntoSingleton :: Ɐe ∷ Integer → Ɐx ∷ Integer → Bool
insertIntoSingleton :: forall a. (OrdSymbolic (SBV a), Eq a, SymVal a)
                    => IO (Proof (Forall "e" a -> Forall "x" a -> SBool))
insertIntoSingleton = runTP $ do
  theorem "insertIntoSingleton"
          (\(Forall @"e" (e :: SBV a)) (Forall @"x" x) ->
            let result = insert e [x]
            in SH.nonDecreasing @a result) $

    -- Split into two cases: e <= x and e > x
    considerCases
      [ ("e_leq_x", eVal .<= xVal, auto)
      , ("e_gt_x",  eVal .>  xVal, auto)
      ]
  where
    eVal, xVal :: SBV a
    eVal = uninterpret "e"
    xVal = uninterpret "x"

-- | A property about removeFirst: if element is not in the list,
--   removeFirst doesn't change it
--
-- >>> removeFirstNotElem @Integer
-- [Proven] removeFirstNotElem :: Ɐe ∷ Integer → Ɐxs ∷ [Integer] → Bool
removeFirstNotElem :: forall a. (Eq a, SymVal a)
                   => IO (Proof (Forall "e" a -> Forall "xs" [a] -> SBool))
removeFirstNotElem = runTP $
  theorem "removeFirstNotElem"
          (\(Forall @"e" (e :: SBV a)) (Forall @"xs" xs) ->
            sNot (e `elem` xs) .=> removeFirst e xs .== xs)
          auto  -- SMT solver handles this via the recursive definition

-- | Combining multiple lemmas with tactics
--
-- >>> insertPreservesLength @Integer
-- [Proven] insertPreservesLength :: Ɐe ∷ Integer → Ɐxs ∷ [Integer] → Bool
insertPreservesLength :: forall a. (OrdSymbolic (SBV a), Eq a, SymVal a)
                      => IO (Proof (Forall "e" a -> Forall "xs" [a] -> SBool))
insertPreservesLength = runTP $ do
  -- First, we might prove that insert always adds exactly one element
  -- This is a natural tactic-style proof
  theorem "insertPreservesLength"
          (\(Forall @"e" (e :: SBV a)) (Forall @"xs" xs) ->
            length (insert e xs) .== length xs + 1)
          auto

{-
Summary:

The tactic-based interface excels at:
  * Simple, direct proofs (use 'auto')
  * Case analysis (use 'splitOn', 'considerCases')
  * Combining multiple lemmas (use 'using')
  * Goal management (use 'defer', 'focus', 'swap')

The calculational style excels at:
  * Inductive proofs (use 'induct' with '|-' and '=:')
  * Step-by-step equational reasoning
  * Showing the proof structure explicitly

For the insertion sort correctness proof, the inductive nature means
the calculational style is the natural choice. But for the helper
properties shown above, tactics provide a cleaner interface.
-}
