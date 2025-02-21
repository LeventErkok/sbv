-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A variety of KnuckleDragger proofs on list processing functions.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Prelude (IO, ($), Integer, Num(..), pure, id, (.), flip)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Data.SBV
-- >>> import Control.Exception
#endif

-- | Data declaration for an uninterpreted type, usually indicating source.
data A
mkUninterpretedSort ''A

-- | Data declaration for an uninterpreted type, usually indicating target.
data B
mkUninterpretedSort ''B

-- | Data declaration for an uninterpreted type, usually indicating an intermediate value.
data C
mkUninterpretedSort ''C

-- * Appending null

-- | @xs ++ [] == xs@
--
-- We have:
--
-- >>> appendNull
-- Lemma: appendNull                       Q.E.D.
-- [Proven] appendNull
appendNull :: IO Proof
appendNull = runKD $ lemma "appendNull" (\(Forall @"xs" (xs :: SList A)) -> xs ++ nil .== xs) []

-- * Moving cons over append

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- We have:
--
-- >>> consApp
-- Lemma: consApp                          Q.E.D.
-- [Proven] consApp
consApp :: IO Proof
consApp = runKD $ lemma "consApp" (\(Forall @"x" (x :: SA)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys)) []

-- * Associativity of append

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- We have:
--
-- >>> appendAssoc
-- Lemma: appendAssoc                      Q.E.D.
-- [Proven] appendAssoc
--
-- Surprisingly, z3 can prove this without any induction. (Since SBV's append translates directly to
-- the concatenation of sequences in SMTLib, it must trigger an internal heuristic in z3
-- that proves it right out-of-the-box!)
appendAssoc :: IO Proof
appendAssoc = runKD $
   lemma "appendAssoc" (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) (Forall @"zs" zs) -> xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs) []

-- * Reverse and append

-- | @reverse (x:xs) == reverse xs ++ [x]@
--
-- >>> revCons
-- Lemma: revCons                          Q.E.D.
-- [Proven] revCons
revCons :: IO Proof
revCons = runKD $ lemma "revCons" (\(Forall @"x" (x :: SA)) (Forall @"xs" xs) -> reverse (x .: xs) .== reverse xs ++ singleton x) []

-- | @reverse (xs ++ ys) .== reverse ys ++ reverse xs@
--
-- We have:
--
-- >>> revApp
-- Inductive lemma: revApp
--   Base: revApp.Base                     Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: revApp.Step                     Q.E.D.
-- [Proven] revApp
revApp :: IO Proof
revApp = runKD $
   induct "revApp"
          (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> reverse (xs ++ ys) .== reverse ys ++ reverse xs) $
          \ih (x :: SA) xs ys -> [] |- reverse ((x .: xs) ++ ys)
                                    =: reverse (x .: (xs ++ ys))
                                    =: reverse (xs ++ ys) ++ singleton x           ? ih
                                    =: (reverse ys ++ reverse xs) ++ singleton x
                                    =: reverse ys ++ (reverse xs ++ singleton x)
                                    =: reverse ys ++ reverse (x .: xs)
                                    =: qed

-- * Reversing twice is identity

-- | @reverse (reverse xs) == xs@
--
-- We have:
--
-- >>> reverseReverse
-- Inductive lemma: revApp
--   Base: revApp.Base                     Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: revApp.Step                     Q.E.D.
-- Inductive lemma: reverseReverse
--   Base: reverseReverse.Base             Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: reverseReverse.Step             Q.E.D.
-- [Proven] reverseReverse
reverseReverse :: IO Proof
reverseReverse = runKD $ do

   ra <- use revApp

   induct "reverseReverse"
          (\(Forall @"xs" (xs :: SList A)) -> reverse (reverse xs) .== xs) $
          \ih (x :: SA) xs -> [] |- reverse (reverse (x .: xs))
                                 =: reverse (reverse xs ++ singleton x)           ? ra
                                 =: reverse (singleton x) ++ reverse (reverse xs) ? ih
                                 =: singleton x ++ xs
                                 =: x .: xs
                                 =: qed

-- * Lengths of lists

-- | @length (x : xs) = 1 + length xs@
--
-- We have:
--
-- >>> lengthTail
-- Lemma: lengthTail                       Q.E.D.
-- [Proven] lengthTail
lengthTail :: IO Proof
lengthTail = runKD $ lemma "lengthTail" (\(Forall @"x" (x :: SA)) (Forall @"xs" xs) -> length (x .: xs) .== 1 + length xs) []

-- | It is instructive to see what kind of counter-example we get if a lemma fails to prove.
-- Below, we do a variant of the 'lengthTail, but with a bad implementation over integers,
-- and see the counter-example. Our implementation returns an incorrect answer if the given list is longer
-- than 5 elements and have 42 in it. We have:
--
-- >>> badLengthProof `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badLengthProof
-- *** Failed to prove badLengthProof.
-- Falsifiable. Counter-example:
--   xs   = [15,11,13,16,27,42] :: [Integer]
--   imp  =                  42 :: Integer
--   spec =                   6 :: Integer
badLengthProof :: IO ()
badLengthProof = runKD $ do
   let badLength :: SList Integer -> SInteger
       badLength xs = ite (length xs .> 5 .&& 42 `elem` xs) 42 (length xs)

   lemma "badLengthProof" (\(Forall @"xs" xs) -> observe "imp" (badLength xs) .== observe "spec" (length xs)) []

   pure ()

-- | @length (xs ++ ys) == length xs + length ys@
--
-- We have:
--
-- >>> lenAppend
-- Lemma: lenAppend                        Q.E.D.
-- [Proven] lenAppend
lenAppend :: IO Proof
lenAppend = runKD $ lemma "lenAppend" (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> length (xs ++ ys) .== length xs + length ys) []

-- | @length xs == length ys -> length (xs ++ ys) == 2 * length xs@
--
-- We have:
--
-- >>> lenAppend2
-- Lemma: lenAppend2                       Q.E.D.
-- [Proven] lenAppend2
lenAppend2 :: IO Proof
lenAppend2 = runKD $
    lemma "lenAppend2" (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> length xs .== length ys .=> length (xs ++ ys) .== 2 * length xs) []

-- * Any, all, and filtering

-- | @not (all id xs) == any not xs@
--
-- A list of booleans is not all true, if any of them is false. We have:
--
-- >>> allAny
-- Inductive lemma: allAny
--   Base: allAny.Base                     Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: allAny.Step                     Q.E.D.
-- [Proven] allAny
allAny :: IO Proof
allAny = runKD $
   induct "allAny"
          (\(Forall @"xs" xs) -> sNot (all id xs) .== any sNot xs) $
          \ih x xs -> [] |- sNot (all id (x .: xs))
                         =: sNot (x .&& all id xs)
                         =: (sNot x .|| sNot (all id xs))   ? ih
                         =: sNot x .|| any sNot xs
                         =: any sNot (x .: xs)
                         =: qed

-- | If an integer list doesn't have 2 as an element, then filtering for @> 2@ or @.>= 2@
-- yields the same result. We have:
--
-- >>> filterEx
-- Inductive lemma: filterEx
--   Base: filterEx.Base                   Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: filterEx.Step                   Q.E.D.
-- [Proven] filterEx
filterEx :: IO Proof
filterEx = runKD $
  induct "filterEx"
         (\(Forall @"xs" xs) -> (2 :: SInteger) `notElem` xs .=> (filter (.> 2) xs .== filter (.>= 2) xs)) $
         \ih x xs -> let h = (2 :: SInteger) `notElem` (x .:  xs)
                  in [h] |- filter (.> 2) (x .: xs)
                         =: ite (x .> 2) (x .: filter (.>  2) xs) (filter (.>  2) xs) ? [hyp h, hprf ih]
                         =: ite (x .> 2) (x .: filter (.>= 2) xs) (filter (.>= 2) xs)
                         =: qed

-- | The 'filterEx' example above, except we get a counter-example if @2@ can be in the list. Note that
-- we don't need the induction tactic here.
--
-- >>> filterEx2 `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: filterEx2
-- *** Failed to prove filterEx2.
-- Falsifiable. Counter-example:
--   xs = [2] :: [Integer]
filterEx2 :: IO ()
filterEx2 = runKD $ do
        lemma "filterEx2" (\(Forall @"xs" xs) -> filter (.> (2 :: SInteger)) xs .== filter (.>= 2) xs) []

        pure ()

-- * Map, append, and reverse

-- | @map f (xs ++ ys) == map f xs ++ map f ys@
--
-- >>> mapAppend (uninterpret "f")
-- Inductive lemma: mapAppend
--   Base: mapAppend.Base                  Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: mapAppend.Step                  Q.E.D.
-- [Proven] mapAppend
mapAppend :: (SA -> SB) -> IO Proof
mapAppend f = runKD $ do
   induct "mapAppend"
          (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> map f (xs ++ ys) .== map f xs ++ map f ys) $
          \ih x xs ys -> [] |- map f ((x .: xs) ++ ys)
                            =: map f (x .: (xs ++ ys))
                            =: f x .: map f (xs ++ ys)        ? ih
                            =: f x .: (map f xs  ++ map f ys)
                            =: (f x .: map f xs) ++ map f ys
                            =: map f (x .: xs) ++ map f ys
                            =: qed

-- | @map f . reverse == reverse . map f@
--
-- >>> mapReverse
-- Inductive lemma: mapAppend
--   Base: mapAppend.Base                  Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: mapAppend.Step                  Q.E.D.
-- Inductive lemma: mapReverse
--   Base: mapReverse.Base                 Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: mapReverse.Step                 Q.E.D.
-- [Proven] mapReverse
mapReverse :: IO Proof
mapReverse = runKD $ do
     let -- For an arbitrary uninterpreted function 'f':
         f :: SA -> SB
         f = uninterpret "f"

     mApp <- use (mapAppend f)

     induct "mapReverse"
            (\(Forall @"xs" xs) -> reverse (map f xs) .== map f (reverse xs)) $
            \ih x xs -> [] |- reverse (map f (x .: xs))
                           =: reverse (f x .: map f xs)
                           =: reverse (map f xs) ++ singleton (f x)       ? ih
                           =: map f (reverse xs) ++ singleton (f x)
                           =: map f (reverse xs) ++ map f (singleton x)   ? mApp
                           =: map f (reverse xs ++ singleton x)
                           =: map f (reverse (x .: xs))
                           =: qed

-- * Reverse and length

-- | @length xs == length (reverse xs)@
--
-- We have:
--
-- >>> revLen
-- Inductive lemma: revLen
--   Base: revLen.Base                     Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: revLen.Step                     Q.E.D.
-- [Proven] revLen
revLen :: IO Proof
revLen = runKD $
   induct "revLen"
          (\(Forall @"xs" (xs :: SList A)) -> length (reverse xs) .== length xs) $
          \ih (x :: SA) xs -> [] |- length (reverse (x .: xs))
                                 =: length (reverse xs ++ singleton x)
                                 =: length (reverse xs) + length (singleton x)  ? ih
                                 =: length xs + 1
                                 =: length (x .: xs)
                                 =: qed

-- | An example where we attempt to prove a non-theorem. Notice the counter-example
-- generated for:
--
-- @length xs = ite (length xs .== 3) 5 (length xs)@
--
-- We have:
--
-- >>> badRevLen `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badRevLen
-- *** Failed to prove badRevLen.
-- Falsifiable. Counter-example:
--   xs = [A_1,A_2,A_1] :: [A]
badRevLen :: IO ()
badRevLen = runKD $ do
   lemma "badRevLen" (\(Forall @"xs" (xs :: SList A)) -> length (reverse xs) .== ite (length xs .== 3) 5 (length xs)) []

   pure ()

-- * Foldr-map fusion

-- | @foldr f a . map g = foldr (f . g) a@
--
-- We have:
--
-- >>> foldrMapFusion
-- Inductive lemma: foldrMapFusion
--   Base: foldrMapFusion.Base             Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: foldrMapFusion.Step             Q.E.D.
-- [Proven] foldrMapFusion
foldrMapFusion :: IO Proof
foldrMapFusion = runKD $ do
  let a :: SA
      a = uninterpret "a"

      g :: SC -> SB
      g = uninterpret "g"

      f :: SB -> SA -> SA
      f = uninterpret "f"

  induct "foldrMapFusion"
         (\(Forall @"xs" xs) -> foldr f a (map g xs) .== foldr (f . g) a xs) $
         \ih x xs -> [] |- foldr f a (map g (x .: xs))
                        =: foldr f a (g x .: map g xs)
                        =: g x `f` foldr f a (map g xs) ? ih
                        =: g x `f` foldr (f . g) a xs
                        =: foldr (f . g) a (x .: xs)
                        =: qed

-- * Foldr-foldr fusion

-- |
--
-- @
--   Given f a = b and f (g x y) = h x (f y), for all x and y
--   We have: f . foldr g a = foldr h b
-- @
--
-- >>> foldrFusion
-- Inductive lemma: foldrFusion
--   Base: foldrFusion.Base                Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: foldrFusion.Step                Q.E.D.
-- [Proven] foldrFusion
foldrFusion :: IO Proof
foldrFusion = runKD $ do
   let a :: SA
       a = uninterpret "a"

       b :: SB
       b = uninterpret "b"

       f :: SA -> SB
       f = uninterpret "f"

       g :: SC -> SA -> SA
       g = uninterpret "g"

       h :: SC -> SB -> SB
       h = uninterpret "h"

       -- Assumptions under which the equality holds
       h1 = f a .== b
       h2 = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) -> f (g x y) .== h x (f y)

   induct "foldrFusion"
          (\(Forall @"xs" xs) -> h1 .&& h2 .=> f (foldr g a xs) .== foldr h b xs) $
          \ih x xs -> [h1, h2] |- f (foldr g a (x .: xs))
                               =: f (g x (foldr g a xs))   ? h2
                               =: h x (f (foldr g a xs))   ? [hyp h1, hyp h2, hprf ih]
                               =: h x (foldr h b xs)
                               =: foldr h b (x .: xs)
                               =: qed

-- * Foldr over append

-- | @foldr f a (xs ++ ys) == foldr f (foldr f a ys) xs@
--
-- We have:
--
-- >>> foldrOverAppend
-- Inductive lemma: foldrOverAppend
--   Base: foldrOverAppend.Base            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: foldrOverAppend.Step            Q.E.D.
-- [Proven] foldrOverAppend
foldrOverAppend :: IO Proof
foldrOverAppend = runKD $ do
   let a :: SA
       a = uninterpret "a"

       f :: SA -> SA -> SA
       f = uninterpret "f"

   induct "foldrOverAppend"
          (\(Forall @"xs" xs) (Forall @"ys" ys) -> foldr f a (xs ++ ys) .== foldr f (foldr f a ys) xs) $
          \ih x xs ys -> [] |- foldr f a ((x .: xs) ++ ys)
                            =: foldr f a (x .: (xs ++ ys))
                            =: x `f` foldr f a (xs ++ ys)       ? ih
                            =: x `f` foldr f (foldr f a ys) xs
                            =: foldr f (foldr f a ys) (x .: xs)
                            =: qed

-- * Foldl over append

-- | @foldl f a (xs ++ ys) == foldl f (foldl f a xs) ys@
--
-- We have:
--
-- >>> foldlOverAppend (uninterpret "f")
-- Inductive lemma: foldlOverAppend
--   Base: foldlOverAppend.Base            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: foldlOverAppend.Step            Q.E.D.
-- [Proven] foldlOverAppend
foldlOverAppend :: (SB -> SA -> SB) -> IO Proof
foldlOverAppend f = runKD $
   -- z3 is smart enough to instantiate the IH correctly below, and the at clause isn't necessary. But we're being
   -- explicit here to emphasize that the IH is used at a different value of a.
   induct "foldlOverAppend"
          (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"a" a) -> foldl f a (xs ++ ys) .== foldl f (foldl f a xs) ys) $
          \ih x xs ys a -> [] |- foldl f a ((x .: xs) ++ ys)
                              =: foldl f a (x .: (xs ++ ys))
                              =: foldl f (a `f` x) (xs ++ ys)       ? ih `at` (Inst @"ys" ys, Inst @"a" (a `f` x))
                              =: foldl f (foldl f (a `f` x) xs) ys
                              =: qed

-- * Foldr-foldl correspondence

-- | @foldr f e xs == foldl (flip f) e (reverse xs)@
--
-- We have:
--
-- >>> foldrFoldlDuality
-- Inductive lemma: foldlOverAppend
--   Base: foldlOverAppend.Base            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: foldlOverAppend.Step            Q.E.D.
-- Inductive lemma: foldrFoldlDuality
--   Base: foldrFoldlDuality.Base          Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: foldrFoldlDuality.Step          Q.E.D.
-- [Proven] foldrFoldlDuality
foldrFoldlDuality :: IO Proof
foldrFoldlDuality = runKD $ do
   let f :: SA -> SB -> SB
       f = uninterpret "f"

   foa <- use (foldlOverAppend (flip f))

   induct "foldrFoldlDuality"
          (\(Forall @"xs" xs) (Forall @"e" e) -> foldr f e xs .== foldl (flip f) e (reverse xs)) $
          \ih x xs e ->
              let ff  = flip f
                  rxs = reverse xs
              in [] |- foldr f e (x .: xs) =: x `f` foldr f e xs                      ? ih
                                           =: x `f` foldl ff e rxs
                                           =: foldl ff e rxs `ff` x
                                           =: foldl ff (foldl ff e rxs) (singleton x) ? foa
                                           =: foldl ff e (rxs ++ singleton x)
                                           =: foldl ff e (reverse (x .: xs))
                                           =: qed

-- * Foldr-foldl duality, generalized

-- | Given:
--
-- @
--     x \@ (y \@ z) = (x \@ y) \@ z     (associativity of @)
-- and e \@ x = x                     (left unit)
-- and x \@ e = x                     (right unit)
-- @
--
-- Prove:
--
-- @
--     foldr (\@) e xs = foldl (\@) e xs
-- @
--
-- We have:
--
-- >>> foldrFoldlDualityGeneralized
-- Inductive lemma: helper
--   Base: helper.Base                     Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: helper.Step                     Q.E.D.
-- Inductive lemma: foldrFoldlDuality
--   Base: foldrFoldlDuality.Base          Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Asms: 5                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: foldrFoldlDuality.Step          Q.E.D.
-- [Proven] foldrFoldlDuality
foldrFoldlDualityGeneralized :: IO Proof
foldrFoldlDualityGeneralized  = runKD $ do
   let (@) :: SA -> SA -> SA
       (@) = uninterpret "|@|"

       e :: SA
       e = uninterpret "e"

   -- Assumptions under which the equality holds
   let assoc = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x @ (y @ z) .== (x @ y) @ z
       lunit = quantifiedBool $ \(Forall @"x" x) -> e @ x .== x
       runit = quantifiedBool $ \(Forall @"x" x) -> x @ e .== x

   -- Helper: foldl (@) (y @ z) xs = y @ foldl (@) z xs
   -- Note the instantiation of the IH at a different value for z. It turns out
   -- we don't have to actually specify this since z3 can figure it out by itself, but we're being explicit.
   helper <- induct "helper"
                     (\(Forall @"xs" xs) (Forall @"y" y) (Forall @"z" z) -> assoc .=> foldl (@) (y @ z) xs .== y @ foldl (@) z xs) $
                     \ih x xs y z -> [assoc] |- foldl (@) (y @ z) (x .: xs)
                                             =: foldl (@) ((y @ z) @ x) xs  ? assoc
                                             =: foldl (@) (y @ (z @ x)) xs  ? [hyp assoc, hprf (ih `at` (Inst @"y" y, Inst @"z" (z @ x)))]
                                             =: y @ foldl (@) (z @ x) xs
                                             =: y @ foldl (@) z (x .: xs)
                                             =: qed

   induct "foldrFoldlDuality"
          (\(Forall @"xs" xs) -> assoc .&& lunit .&& runit .=> foldr (@) e xs .== foldl (@) e xs) $
          \ih x xs -> [assoc, lunit, runit] |- foldr (@) e (x .: xs)
                                            =: x @ foldr (@) e xs    ? [hyp assoc, hyp lunit, hyp runit, hprf ih]
                                            =: x @ foldl (@) e xs    ? [hyp assoc, hprf helper]
                                            =: foldl (@) (x @ e) xs  ? runit
                                            =: foldl (@) x xs        ? lunit
                                            =: foldl (@) (e @ x) xs
                                            =: foldl (@) e (x .: xs)
                                            =: qed

-- * Another foldl-foldr correspondence

-- | Given:
--
-- @
--        (x \<+> y) \<*> z = x \<+> (y \<*> z)
--   and  x \<+> e = e \<*> x
-- @
--
-- Proves:
--
-- @
--    foldr (\<+>) e xs = foldl (\<*>) e xs
-- @
--
-- In Bird's Introduction to Functional Programming book (2nd edition) this is called the second duality theorem. We have:
--
-- >>> foldrFoldl
-- Inductive lemma: foldl over <*>/<+>
--   Base: foldl over <*>/<+>.Base         Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: foldl over <*>/<+>.Step         Q.E.D.
-- Inductive lemma: foldrFoldl
--   Base: foldrFoldl.Base                 Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: foldrFoldl.Step                 Q.E.D.
-- [Proven] foldrFoldl
foldrFoldl :: IO Proof
foldrFoldl = runKD $ do

   let -- Declare the operators as uninterpreted functions
       (<+>) :: SA -> SB -> SB
       (<+>) = uninterpret "<+>"

       (<*>) :: SB -> SA -> SB
       (<*>) = uninterpret "<*>"

       -- The unit element
       e :: SB
       e = uninterpret "e"

   -- Assumptions about the operators
   let -- (x <+> y) <*> z == x <+> (y <*> z)
       assoc = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> (x <+> y) <*> z .== x <+> (y <*> z)

       -- x <+> e == e <*> x
       unit  = quantifiedBool $ \(Forall @"x" x) -> x <+> e .== e <*> x

   -- Helper: x <+> foldl (<*>) y xs == foldl (<*>) (x <+> y) xs
   helper <-
      induct "foldl over <*>/<+>"
             (\(Forall @"xs" xs) (Forall @"x" x) (Forall @"y" y) -> assoc .=> x <+> foldl (<*>) y xs .== foldl (<*>) (x <+> y) xs) $
             -- Using z to avoid confusion with the variable x already present, following Bird.
             -- z3 can figure out the proper instantiation of ih so the at call is unnecessary, but being explicit is helpful.
             \ih z xs x y -> [assoc] |- x <+> foldl (<*>) y (z .: xs)
                                     =: x <+> foldl (<*>) (y <*> z) xs    ? [hyp assoc, hprf (ih `at` (Inst @"x" x, Inst @"y" (y <*> z)))]
                                     =: foldl (<*>) (x <+> (y <*> z)) xs  ? assoc
                                     =: foldl (<*>) ((x <+> y) <*> z) xs
                                     =: foldl (<*>) (x <+> y) (z .: xs)
                                     =: qed

   -- Final proof:
   induct "foldrFoldl"
          (\(Forall @"xs" xs) -> assoc .&& unit .=> foldr (<+>) e xs .== foldl (<*>) e xs) $
          \ih x xs -> [assoc, unit] |- foldr (<+>) e (x .: xs)
                                    =: x <+> foldr (<+>) e xs    ? [hyp assoc, hyp unit, hprf ih]
                                    =: x <+> foldl (<*>) e xs    ? [hyp assoc, hprf helper]
                                    =: foldl (<*>) (x <+> e) xs  ? unit
                                    =: foldl (<*>) (e <*> x) xs
                                    =: foldl (<*>) e (x .: xs)
                                    =: qed

-- * Bookkeeping law

-- | Provided @f@ is associative and @a@ is its both left and right-unit:
--
-- @foldr f a . concat == foldr f a . map (foldr f a)@
--
-- We have:
--
-- >>> bookKeeping
-- Inductive lemma: foldBase
--   Base: foldBase.Base                   Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: foldBase.Step                   Q.E.D.
-- Inductive lemma: foldrOverAppend
--   Base: foldrOverAppend.Base            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: foldrOverAppend.Step            Q.E.D.
-- Inductive lemma: bookKeeping
--   Base: bookKeeping.Base                Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: bookKeeping.Step                Q.E.D.
-- [Proven] bookKeeping
--
-- NB. As of early 2025, we cannot express the above theorem in SBV directly, since it involves nested lambdas.
-- (On the right hand side map has an argument that is represented as a foldr, which itself has a lambda.) As
-- SMTLib moves to a higher-order logic, we intend to make such expressions readily expressable. In the mean time,
-- we use an equivalent (albeit roundabout) version, where we define map-foldr combo as a recursive function ourselves.
--
-- NB. This theorem does not hold if @f@ does not have a left-unit! Consider the input @[[], [x]]@. Left hand side reduces to
-- @x@, while the right hand side reduces to: @f a x@. And unless @f@ is commutative or @a@ is not also a left-unit,
-- then one can find a counter-example. (Aside: if both left and right units exist for a binary operator, then they
-- are necessarily the same element, since @l = f l r = r@. So, an equivalent statement could simply say @f@ has
-- both left and right units.) A concrete counter-example is:
--
-- @
--   data T = A | B | C
--
--   f :: T -> T -> T
--   f C A = A
--   f C B = A
--   f x _ = x
-- @
--
-- You can verify @f@ is associative. Also note that @C@ is the right-unit for @f@, but it isn't the left-unit.
-- In fact, @f@ has no-left unit by the above argument. In this case, the bookkeeping law produces @B@ for
-- the left-hand-side, and @A@ for the right-hand-side for the input @[[], [B]]@.
bookKeeping :: IO Proof
bookKeeping = runKD $ do
   let a :: SA
       a = uninterpret "a"

       f :: SA -> SA -> SA
       f = uninterpret "f"

       -- Fuse map (foldr f a) in the theorem into one call to avoid nested lambdas. See above note.
       mapFoldr :: SA -> SList [A] -> SList A
       mapFoldr = smtFunction "mapFoldr" $ \e xss -> ite (null xss)
                                                         nil
                                                         (foldr f e (head xss) .: mapFoldr e (tail xss))

   -- Assumptions about f
   let assoc = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x `f` (y `f` z) .== (x `f` y) `f` z
       rUnit = quantifiedBool $ \(Forall @"x" x) -> x `f` a .== x
       lUnit = quantifiedBool $ \(Forall @"x" x) -> a `f` x .== x

   -- Helper:
   --   foldr f y xs = foldr f a xs `f` y
   helper <- induct "foldBase"
                    (\(Forall @"xs" xs) (Forall @"y" y) -> lUnit .&& assoc .=> foldr f y xs .== foldr f a xs `f` y) $
                    \ih x xs y -> [lUnit, assoc] |- foldr f y (x .: xs)
                                                 =: x `f` foldr f y xs          ? [hyp lUnit, hyp assoc, hprf ih]
                                                 =: x `f` (foldr f a xs `f` y)  ? assoc
                                                 =: (x `f` foldr f a xs) `f` y
                                                 =: foldr f a (x .: xs) `f` y
                                                 =: qed

   foa <- use foldrOverAppend

   induct "bookKeeping"
          (\(Forall @"xss" xss) -> assoc .&& rUnit .&& lUnit .=> foldr f a (concat xss) .== foldr f a (mapFoldr a xss)) $
          \ih xs xss -> [assoc, rUnit, lUnit] |- foldr f a (concat (xs .: xss))
                                              =: foldr f a (xs ++ concat xss)                 ? foa
                                              =: foldr f (foldr f a (concat xss)) xs          ? [hyp assoc, hyp rUnit, hyp lUnit, hprf ih]
                                              =: foldr f (foldr f a (mapFoldr a xss)) xs      ? [hyp lUnit, hyp assoc, hprf (helper `at` (Inst @"xs" xs, Inst @"y" (foldr f a (mapFoldr a xss))))]
                                              =: foldr f a xs `f` foldr f a (mapFoldr a xss)
                                              =: foldr f a (foldr f a xs .: mapFoldr a xss)
                                              =: foldr f a (mapFoldr a (xs .: xss))
                                              =: qed

-- * Filter-append

-- | @filter f (xs ++ ys) == filter f xs ++ filter f ys@
--
-- We have:
--
-- >>> filterAppend
-- Inductive lemma: filterAppend
--   Base: filterAppend.Base               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: filterAppend.Step               Q.E.D.
-- [Proven] filterAppend
filterAppend :: IO Proof
filterAppend = runKD $ do
   let -- For an arbitrary uninterpreted predicate 'f':
       f :: SA -> SBool
       f = uninterpret "f"

   induct "filterAppend"
          (\(Forall @"xs" xs) (Forall @"ys" ys) -> filter f xs ++ filter f ys .== filter f (xs ++ ys)) $
          \ih x xs ys -> [] |- filter f (x .: xs) ++ filter f ys
                            =: ite (f x) (x .: filter f xs) (filter f xs) ++ filter f ys
                            =: ite (f x) (x .: filter f xs ++ filter f ys) (filter f xs ++ filter f ys)  ? ih
                            =: ite (f x) (x .: filter f (xs ++ ys)) (filter f (xs ++ ys))
                            =: filter f (x .: (xs ++ ys))
                            =: filter f ((x .: xs) ++ ys)
                            =: qed

-- * Map and filter don't commute

-- | In general, mapping and filtering operations do not commute. We'll see the kind of counter-example we get from SBV if
-- we attempt to prove:
--
-- >>> mapFilter `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badMapFilter
-- *** Failed to prove badMapFilter.
-- Falsifiable. Counter-example:
--   xs  = [A_3] :: [A]
--   lhs = [A_0] :: [A]
--   rhs =    [] :: [A]
-- <BLANKLINE>
--   f :: A -> A
--   f _ = A_0
-- <BLANKLINE>
--   p :: A -> Bool
--   p A_3 = True
--   p _   = False
--
-- As expected, the function @f@ maps everything to @A_0@, and the predicate @p@ only lets @A_3@ through. As shown in the
-- counter-example, for the input @[A_3]@, left-hand-side filters nothing and the result is the singleton @A_0@. But the
-- map on the right-hand side maps everything to @[A_0]@ and the filter gets rid of the elements, resulting in an empty list.
mapFilter :: IO ()
mapFilter = runKD $ do
   let f :: SA -> SA
       f = uninterpret "f"

       p :: SA -> SBool
       p = uninterpret "p"

   lemma "badMapFilter"
          (\(Forall @"xs" xs) -> observe "lhs" (map f (filter p xs)) .== observe "rhs" (filter p (map f xs)))
          []

   pure ()
