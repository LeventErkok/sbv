-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Queue
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A classic functional queue implemented with two stacks (lists). The front
-- list holds elements ready for dequeue; the back list accumulates new
-- elements in reverse. We prove that this representation faithfully
-- implements a FIFO queue by showing:
--
--   (1) Enqueue appends to the abstract queue.
--   (2) Enqueuing a sequence of elements and reading out the abstraction
--       gives back the original sequence.
--   (3) Dequeue retrieves the front of the abstract queue.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Queue where

import Prelude hiding (length, head, tail, null, reverse, (++), fst, snd)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.SBV.Tuple
-- >>> import Data.SBV.TP
#endif

-- * Queue representation

-- | A queue is a pair @(front, back)@ representing the abstract list
-- @front ++ reverse back@.
type Queue a = STuple [a] [a]

-- | Abstraction function: the list a queue represents.
--
-- >>> toList (tuple ([1,2,3], [6,5,4])) :: SList Integer
-- [1,2,3,4,5,6] :: [SInteger]
toList :: SymVal a => Queue a -> SList a
toList q = [sCase| q of
               (f, b) -> f ++ reverse b
           |]

-- | The empty queue.
--
-- >>> toList (emptyQ @Integer)
-- [] :: [SInteger]
emptyQ :: SymVal a => Queue a
emptyQ = tuple ([], [])

-- | Enqueue: add an element to the back.
--
-- >>> toList (enqueue (tuple ([1,2], [4,3])) 5) :: SList Integer
-- [1,2,3,4,5] :: [SInteger]
enqueue :: SymVal a => Queue a -> SBV a -> Queue a
enqueue q x = [sCase| q of
                  (f, b) -> tuple (f, x .: b)
              |]

-- | Enqueue all elements of a list, left to right.
--
-- >>> toList (enqueueAll (emptyQ @Integer) [1,2,3])
-- [1,2,3] :: [SInteger]
enqueueAll :: SymVal a => Queue a -> SList a -> Queue a
enqueueAll = smtFunction "enqueueAll"
           $ \q xs -> [sCase| xs of
                         []       -> q
                         x : rest -> enqueueAll (enqueue q x) rest
                      |]

-- | Dequeue: remove and return the front element. When the front list
-- is empty, we reverse the back list into the front first.
-- Precondition: the queue is non-empty.
--
-- >>> let (v, q') = untuple (dequeue (tuple ([1,2,3], [6,5,4]) :: Queue Integer)) in (v, toList q')
-- (1 :: SInteger,[2,3,4,5,6] :: [SInteger])
-- >>> let (v, q') = untuple (dequeue (tuple ([], [3,2,1]) :: Queue Integer)) in (v, toList q')
-- (1 :: SInteger,[2,3] :: [SInteger])
dequeue :: forall a. SymVal a => Queue a -> STuple a ([a], [a])
dequeue q = [sCase| q of
               (x : xs, t) -> tuple (x, tuple (xs, t))
               ([],     t) -> case reverse t of
                                y : ys -> tuple (y, tuple (ys, []))
                                -- unreachable: both front and back are empty
                                _      -> tuple (some "dead" (const sTrue), tuple ([], []))
            |]

-- * Correctness

-- | @toList (enqueue q x) == toList q ++ [x]@
--
-- Enqueue appends to the abstract list.
--
-- >>> runTP $ enqueueCorrect @Integer
-- Lemma: enqueueCorrect    Q.E.D.
-- Functions proven terminating: sbv.reverse
-- [Proven] enqueueCorrect :: Ɐf ∷ [Integer] → Ɐb ∷ [Integer] → Ɐx ∷ Integer → Bool
enqueueCorrect :: forall a. SymVal a => TP (Proof (Forall "f" [a] -> Forall "b" [a] -> Forall "x" a -> SBool))
enqueueCorrect =
   lemma "enqueueCorrect"
         (\(Forall @"f" f) (Forall @"b" b) (Forall @"x" x) ->
              toList (enqueue (tuple (f, b)) x) .== toList (tuple (f, b)) ++ [x])
         []

-- | @toList (enqueueAll q xs) == toList q ++ xs@
--
-- Enqueuing a sequence of elements appends the whole sequence to the
-- abstract list. This is the key invariant of the two-stack representation.
--
-- >>> runTP $ enqueueAllCorrect @Integer
-- Lemma: enqueueCorrect                 Q.E.D.
-- Inductive lemma: enqueueAllCorrect
--   Step: Base                          Q.E.D.
--   Step: 1                             Q.E.D.
--   Step: 2                             Q.E.D.
--   Step: 3                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating: enqueueAll, sbv.reverse
-- [Proven] enqueueAllCorrect :: Ɐxs ∷ [Integer] → Ɐf ∷ [Integer] → Ɐb ∷ [Integer] → Bool
enqueueAllCorrect :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "f" [a] -> Forall "b" [a] -> SBool))
enqueueAllCorrect = do

   eqC <- enqueueCorrect @a

   induct "enqueueAllCorrect"
          (\(Forall @"xs" xs) (Forall @"f" f) (Forall @"b" b) ->
               toList (enqueueAll (tuple (f, b)) xs) .== (f ++ reverse b) ++ xs) $
          \ih (x, xs) f b -> []
                          |- toList (enqueueAll (tuple (f, b)) (x .: xs))
                          =: toList (enqueueAll (tuple (f, x .: b)) xs)
                          ?? ih `at` (Inst @"f" f, Inst @"b" (x .: b))
                          =: (f ++ reverse (x .: b)) ++ xs
                          ?? eqC
                          =: (f ++ reverse b) ++ (x .: xs)
                          =: qed

-- | @toList (enqueueAll emptyQ xs) == xs@
--
-- Starting from an empty queue, enqueuing a list of elements produces
-- a queue whose abstract contents is that same list. This demonstrates
-- the fundamental FIFO property: elements come out in the order they went in.
--
-- >>> runTP $ fifo @Integer
-- Lemma: enqueueAllCorrect              Q.E.D.
-- Lemma: fifo
--   Step: 1                             Q.E.D.
--   Step: 2                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating: enqueueAll, sbv.reverse
-- [Proven] fifo :: Ɐxs ∷ [Integer] → Bool
fifo :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
fifo = do
   eaC <- recall (enqueueAllCorrect @a)

   calc "fifo"
        (\(Forall xs) -> toList (enqueueAll emptyQ xs) .== xs) $
        \xs -> [] |- toList (enqueueAll emptyQ xs)
                  ?? eaC `at` (Inst @"xs" xs, Inst @"f" ([] :: SList a), Inst @"b" ([] :: SList a))
                  =: reverse [] ++ xs
                  =: xs
                  =: qed

-- | Dequeue from a non-empty queue gives the head of the abstract list,
-- and the remaining queue represents the tail.
--
-- >>> runTP $ dequeueCorrect @Integer
-- Lemma: dequeueCorrect    Q.E.D.
-- Functions proven terminating: sbv.reverse
-- [Proven] dequeueCorrect :: Ɐf ∷ [Integer] → Ɐb ∷ [Integer] → Bool
dequeueCorrect :: forall a. SymVal a => TP (Proof (Forall "f" [a] -> Forall "b" [a] -> SBool))
dequeueCorrect =
   lemma "dequeueCorrect"
         (\(Forall @"f" f) (Forall @"b" b) ->
              sNot (null (toList (tuple (f, b))))
              .=> let (v, q) = untuple (dequeue (tuple (f, b)))
                      l      = toList (tuple (f, b))
                  in v .== head l .&& toList q .== tail l)
         []
