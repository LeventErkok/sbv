-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A variety of KnuckleDragger proofs on list processing functions. Note that
-- these proofs only hold for finite lists. SMT-solvers do not model infinite
-- lists, and hence all claims are for finite (but arbitrary-length) lists.
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

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Prelude (IO, ($), Integer, Num(..), id, (.), flip, error)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.Tools.KnuckleDragger

import Control.Monad (void)
import Data.Proxy

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.Proxy
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
                                    =: reverse (xs ++ ys) ++ singleton x           ?? ih
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
                                 =: reverse (reverse xs ++ singleton x)           ?? ra
                                 =: reverse (singleton x) ++ reverse (reverse xs) ?? ih
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

   void $ lemma "badLengthProof" (\(Forall @"xs" xs) -> observe "imp" (badLength xs) .== observe "spec" (length xs)) []

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
                         =: (sNot x .|| sNot (all id xs))   ?? ih
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
                         =: ite (x .> 2) (x .: filter (.>  2) xs) (filter (.>  2) xs) ?? [hyp h, hprf ih]
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
filterEx2 = runKD $
   void $ lemma "filterEx2" (\(Forall @"xs" xs) -> filter (.> (2 :: SInteger)) xs .== filter (.>= 2) xs) []

-- * Map, append, and reverse

-- | @f = g => map f xs = map g xs@
--
-- >>> mapEquiv
-- Inductive lemma: mapEquiv
--   Base: mapEquiv.Base                   Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: mapEquiv.Step                   Q.E.D.
-- [Proven] mapEquiv
mapEquiv :: IO Proof
mapEquiv = runKD $ do
   let f, g :: SA -> SB
       f = uninterpret "f"
       g = uninterpret "g"

       f'eq'g :: SBool
       f'eq'g = quantifiedBool $ \(Forall @"x" x) -> f x .== g x

   induct "mapEquiv"
          (\(Forall @"xs" xs) -> f'eq'g .=> map f xs .== map g xs) $
          \ih x xs -> [f'eq'g] |- map f (x .: xs) .== map g (x .: xs)
                               =: f x .: map f xs .== g x .: map g xs ?? f'eq'g
                               =: f x .: map f xs .== f x .: map g xs ?? [hyp f'eq'g, hprf ih]
                               =: f x .: map f xs .== f x .: map f xs
                               =: map f (x .: xs) .== map f (x .: xs)
                               =: qed

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
                            =: f x .: map f (xs ++ ys)        ?? ih
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
                           =: reverse (map f xs) ++ singleton (f x)       ?? ih
                           =: map f (reverse xs) ++ singleton (f x)
                           =: map f (reverse xs) ++ map f (singleton x)   ?? mApp
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
                                 =: length (reverse xs) + length (singleton x)  ?? ih
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
badRevLen = runKD $
   void $ lemma "badRevLen" (\(Forall @"xs" (xs :: SList A)) -> length (reverse xs) .== ite (length xs .== 3) 5 (length xs)) []

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
                        =: g x `f` foldr f a (map g xs) ?? ih
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
                               =: f (g x (foldr g a xs))   ?? h2
                               =: h x (f (foldr g a xs))   ?? [hyp h1, hyp h2, hprf ih]
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
                            =: x `f` foldr f a (xs ++ ys)       ?? ih
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
   induct "foldlOverAppend"
          (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"a" a) -> foldl f a (xs ++ ys) .== foldl f (foldl f a xs) ys) $
          \ih x xs ys a -> [] |- foldl f a ((x .: xs) ++ ys)
                              =: foldl f a (x .: (xs ++ ys))
                              =: foldl f (a `f` x) (xs ++ ys)
                              -- z3 is smart enough to instantiate the IH correctly below, but we're
                              -- using an explicit instantiation to be clear about the use of @a@ at a different value
                              ?? ih `at` (Inst @"ys" ys, Inst @"a" (a `f` x))
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
              in [] |- foldr f e (x .: xs) =: x `f` foldr f e xs                      ?? ih
                                           =: x `f` foldl ff e rxs
                                           =: foldl ff e rxs `ff` x
                                           =: foldl ff (foldl ff e rxs) (singleton x) ?? foa
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
                                             =: foldl (@) ((y @ z) @ x) xs
                                             ?? assoc
                                             =: foldl (@) (y @ (z @ x)) xs
                                             ?? [hyp assoc, hprf (ih `at` (Inst @"y" y, Inst @"z" (z @ x)))]
                                             =: y @ foldl (@) (z @ x) xs
                                             =: y @ foldl (@) z (x .: xs)
                                             =: qed

   induct "foldrFoldlDuality"
          (\(Forall @"xs" xs) -> assoc .&& lunit .&& runit .=> foldr (@) e xs .== foldl (@) e xs) $
          \ih x xs -> [assoc, lunit, runit] |- foldr (@) e (x .: xs)
                                            =: x @ foldr (@) e xs    ?? [hyp assoc, hyp lunit, hyp runit, hprf ih]
                                            =: x @ foldl (@) e xs    ?? [hyp assoc, hprf helper]
                                            =: foldl (@) (x @ e) xs  ?? runit
                                            =: foldl (@) x xs        ?? lunit
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
                                     =: x <+> foldl (<*>) (y <*> z) xs    ?? [hyp assoc, hprf (ih `at` (Inst @"x" x, Inst @"y" (y <*> z)))]
                                     =: foldl (<*>) (x <+> (y <*> z)) xs  ?? assoc
                                     =: foldl (<*>) ((x <+> y) <*> z) xs
                                     =: foldl (<*>) (x <+> y) (z .: xs)
                                     =: qed

   -- Final proof:
   induct "foldrFoldl"
          (\(Forall @"xs" xs) -> assoc .&& unit .=> foldr (<+>) e xs .== foldl (<*>) e xs) $
          \ih x xs -> [assoc, unit] |- foldr (<+>) e (x .: xs)
                                    =: x <+> foldr (<+>) e xs    ?? [hyp assoc, hyp unit, hprf ih]
                                    =: x <+> foldl (<*>) e xs    ?? [hyp assoc, hprf helper]
                                    =: foldl (<*>) (x <+> e) xs  ?? unit
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
                                                 =: x `f` foldr f y xs          ?? [hyp lUnit, hyp assoc, hprf ih]
                                                 =: x `f` (foldr f a xs `f` y)  ?? assoc
                                                 =: (x `f` foldr f a xs) `f` y
                                                 =: foldr f a (x .: xs) `f` y
                                                 =: qed

   foa <- use foldrOverAppend

   induct "bookKeeping"
          (\(Forall @"xss" xss) -> assoc .&& rUnit .&& lUnit .=> foldr f a (concat xss) .== foldr f a (mapFoldr a xss)) $
          \ih xs xss -> [assoc, rUnit, lUnit] |- foldr f a (concat (xs .: xss))
                                              =: foldr f a (xs ++ concat xss)                 ?? foa
                                              =: foldr f (foldr f a (concat xss)) xs          ?? [hyp assoc, hyp rUnit, hyp lUnit, hprf ih]
                                              =: foldr f (foldr f a (mapFoldr a xss)) xs      ?? [hyp lUnit, hyp assoc, hprf (helper `at` (Inst @"xs" xs, Inst @"y" (foldr f a (mapFoldr a xss))))]
                                              =: foldr f a xs `f` foldr f a (mapFoldr a xss)
                                              =: foldr f a (foldr f a xs .: mapFoldr a xss)
                                              =: foldr f a (mapFoldr a (xs .: xss))
                                              =: qed

-- * Filter-append

-- | @filter p (xs ++ ys) == filter p xs ++ filter p ys@
--
-- We have:
--
-- >>> filterAppend (uninterpret "p")
-- Inductive lemma: filterAppend
--   Base: filterAppend.Base               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: filterAppend.Step               Q.E.D.
-- [Proven] filterAppend
filterAppend :: (SA -> SBool) -> IO Proof
filterAppend p = runKD $
   induct "filterAppend"
          (\(Forall @"xs" xs) (Forall @"ys" ys) -> filter p xs ++ filter p ys .== filter p (xs ++ ys)) $
          \ih x xs ys -> [] |- filter p (x .: xs) ++ filter p ys
                            =: ite (p x) (x .: filter p xs) (filter p xs) ++ filter p ys
                            =: ite (p x) (x .: filter p xs ++ filter p ys) (filter p xs ++ filter p ys)  ?? ih
                            =: ite (p x) (x .: filter p (xs ++ ys)) (filter p (xs ++ ys))
                            =: filter p (x .: (xs ++ ys))
                            =: filter p ((x .: xs) ++ ys)
                            =: qed

-- | @filter p (concat xss) == concatMap (filter p xss)@
--
-- Similar to the book-keeping law, we cannot express this in SBV directly, since it involves a nested lambda.
-- @concatMap (filter p)@ maps a higher-order function @filter p@, which itself has a nested lambda. So, we use
-- our own merged definition. Hopefully we'll relax this as SMTLib gains more higher order features.
--
-- We have:
--
-- >>> filterConcat
-- Inductive lemma: filterAppend
--   Base: filterAppend.Base               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: filterAppend.Step               Q.E.D.
-- Inductive lemma: filterConcat
--   Base: filterConcat.Base               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: filterConcat.Step               Q.E.D.
-- [Proven] filterConcat
filterConcat :: IO Proof
filterConcat = runKD $ do
  let -- For an arbitrary uninterpreted prediate 'p':
      p :: SA -> SBool
      p = uninterpret "p"

      -- Fuse concatMap (filter p) in the theorem to avoid nested lambdas. See above note
      concatMapFilter :: (SA -> SBool) -> SList [A] -> SList A
      concatMapFilter pred = smtFunction "concatMapFilter" $ \xs -> ite (null xs)
                                                                        nil
                                                                        (filter pred (head xs) ++ concatMapFilter pred (tail xs))


  fa <- use $ filterAppend p

  induct "filterConcat"
         (\(Forall @"xss" xss) -> filter p (concat xss) .== concatMapFilter p xss) $
         \ih xs xss -> [] |- filter p (concat (xs .: xss))
                          =: filter p (xs ++ concat xss)           ?? fa
                          =: filter p xs ++ filter p (concat xss)  ?? ih
                          =: filter p xs ++ concatMapFilter p xss
                          =: concatMapFilter p (xs .: xss)
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

   void $ lemma "badMapFilter"
                (\(Forall @"xs" xs) -> observe "lhs" (map f (filter p xs)) .== observe "rhs" (filter p (map f xs)))
                []

-- * Partition

-- | @fst (partition f xs) == filter f xs@
--
-- >>> partition1
-- Inductive lemma: partition1
--   Base: partition1.Base                 Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: partition1.Step                 Q.E.D.
-- [Proven] partition1
partition1 :: IO Proof
partition1 = runKD $ do
   let f :: SA -> SBool
       f = uninterpret "f"

   induct "partition1"
          (\(Forall @"xs" xs) -> fst (partition f xs) .== filter f xs) $
          \ih x xs -> [] |- fst (partition f (x .: xs))
                         =: fst (let res = partition f xs
                                 in ite (f x)
                                        (tuple (x .: fst res, snd res))
                                        (tuple (fst res, x .: snd res)))
                         =: ite (f x) (x .: fst (partition f xs)) (fst (partition f xs)) ?? ih
                         =: ite (f x) (x .: filter f xs) (filter f xs)
                         =: filter f (x .: xs)
                         =: qed

-- | @snd (partition f xs) == filter (not . f) xs@
--
-- >>> partition2
-- Inductive lemma: partition2
--   Base: partition2.Base                 Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: partition2.Step                 Q.E.D.
-- [Proven] partition2
partition2 :: IO Proof
partition2 = runKD $ do
   let f :: SA -> SBool
       f = uninterpret "f"

   induct "partition2"
          (\(Forall @"xs" xs) -> snd (partition f xs) .== filter (sNot . f) xs) $
          \ih x xs -> [] |- snd (partition f (x .: xs))
                         =: snd (let res = partition f xs
                                 in ite (f x)
                                        (tuple (x .: fst res, snd res))
                                        (tuple (fst res, x .: snd res)))
                         =: ite (f x) (snd (partition f xs)) (x .: snd (partition f xs)) ?? ih
                         =: ite (f x) (filter (sNot . f) xs) (x .: filter (sNot . f) xs)
                         =: filter (sNot . f) (x .: xs)
                         =: qed

-- * Take and drop

-- | @take n (take m xs) = take (n `smin` m) xs@
--
-- >>> take_take
-- Lemma: take_take                        Q.E.D.
-- [Proven] take_take
take_take :: IO Proof
take_take = runKD $
   lemma "take_take"
         (\(Forall @"xs" (xs :: SList A)) (Forall @"m" m) (Forall @"n" n) -> take n (take m xs) .== take (n `smin` m) xs)
         []


-- | @n >= 0 && m >= 0 => drop n (drop m xs) = drop (n + m) xs@
--
-- >>> drop_drop
-- Lemma: drop_drop                        Q.E.D.
-- [Proven] drop_drop
drop_drop :: IO Proof
drop_drop = runKD $
   lemma "drop_drop"
          (\(Forall @"n" n) (Forall @"m" m) (Forall @"xs" (xs :: SList A)) ->
                n .>= 0 .&& m .>= 0 .=> drop n (drop m xs) .== drop (n + m) xs)
          []

-- | @take n xs ++ drop n xs == xs@
--
-- >>> take_drop
-- Lemma: take_drop                        Q.E.D.
-- [Proven] take_drop
take_drop :: IO Proof
take_drop = runKD $
    lemma "take_drop"
           (\(Forall @"n" n) (Forall @"xs" (xs :: SList A)) -> take n xs ++ drop n xs .== xs)
           []

-- | @n .> 0 => take n (x .: xs) = x .: take (n - 1) xs@
--
-- >>> take_cons
-- Lemma: take_cons                        Q.E.D.
-- [Proven] take_cons
take_cons :: IO Proof
take_cons = runKD $
   lemma "take_cons"
         (\(Forall @"n" n) (Forall @"x" x) (Forall @"xs" (xs :: SList A)) -> n .> 0 .=> take n (x .: xs) .== x .: take (n - 1) xs)
         []

-- | @take n (map f xs) == map f (take n xs)@
--
-- >>> take_map
-- Lemma: take_cons                        Q.E.D.
-- Lemma: map1                             Q.E.D.
-- Lemma: take_map.n <= 0                  Q.E.D.
-- Inductive lemma: take_map.n > 0
--   Base: take_map.n > 0.Base             Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Asms: 5                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: take_map.n > 0.Step             Q.E.D.
-- Lemma: take_map                         Q.E.D.
-- [Proven] take_map
take_map :: IO Proof
take_map = runKD $ do
    let f :: SA -> SB
        f = uninterpret "f"

    tc   <- use take_cons
    map1 <- lemma "map1" (\(Forall @"x" x) (Forall @"xs" xs) -> map f (x .: xs) .== f x .: map f xs) []

    h1 <- lemma "take_map.n <= 0"
                 (\(Forall @"xs" xs) (Forall @"n" n) -> n .<= 0 .=> take n (map f xs) .== map f (take n xs))
                 []

    h2 <- induct "take_map.n > 0"
                 (\(Forall @"xs" xs) (Forall @"n" n) -> n .> 0 .=> take n (map f xs) .== map f (take n xs)) $
                 \ih x xs n -> [n .> 0] |- take n (map f (x .: xs))
                                        =: take n (f x .: map f xs)       ?? n .> 0
                                        =: f x .: take (n - 1) (map f xs) ?? ih   `at` Inst @"n" (n-1)
                                        =: f x .: map f (take (n - 1) xs) ?? map1 `at` (Inst @"x" x, Inst @"xs" (take (n - 1) xs))
                                        =: map f (x .: take (n - 1) xs)   ?? [hyp (n .> 0), hprf tc]
                                        =: map f (take n (x .: xs))
                                        =: qed

    lemma "take_map" (\(Forall @"xs" xs) (Forall @"n" n) -> take n (map f xs) .== map f (take n xs)) [h1, h2]

-- | @n .> 0 => drop n (x .: xs) = drop (n - 1) xs@
--
-- >>> drop_cons (Proxy @A)
-- Lemma: drop_cons                        Q.E.D.
-- [Proven] drop_cons
drop_cons :: forall elt. SymVal elt => Proxy elt -> IO Proof
drop_cons _ = runKD $
   lemma "drop_cons"
         (\(Forall @"n" n) (Forall @"x" x) (Forall @"xs" (xs :: SList elt)) -> n .> 0 .=> drop n (x .: xs) .== drop (n - 1) xs)
         []

-- | @drop n (map f xs) == map f (drop n xs)@
--
-- >>> drop_map
-- Lemma: drop_cons                        Q.E.D.
-- Lemma: drop_cons                        Q.E.D.
-- Lemma: drop_map.n <= 0                  Q.E.D.
-- Inductive lemma: drop_map.n > 0
--   Base: drop_map.n > 0.Base             Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: drop_map.n > 0.Step             Q.E.D.
-- Lemma: drop_map
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Step  : 3                             Q.E.D.
--   Step  : 4                             Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] drop_map
drop_map :: IO Proof
drop_map = runKD $ do
   let f :: SA -> SB
       f = uninterpret "f"

   dcA <- use $ drop_cons (Proxy @A)
   dcB <- use $ drop_cons (Proxy @B)

   h1 <- lemma "drop_map.n <= 0"
               (\(Forall @"xs" xs) (Forall @"n" n) -> n .<= 0 .=> drop n (map f xs) .== map f (drop n xs))
               []

   h2 <- induct "drop_map.n > 0"
                (\(Forall @"xs" xs) (Forall @"n" n) -> n .> 0 .=> drop n (map f xs) .== map f (drop n xs)) $
                \ih x xs n -> [n .> 0] |- drop n (map f (x .: xs))
                                       =: drop n (f x .: map f xs)
                                       ?? [hyp (n .> 0), hprf (dcB `at` (Inst @"n" n, Inst @"x" (f x), Inst @"xs" (map f xs)))]
                                       =: drop (n - 1) (map f xs)
                                       ?? [hyp (n .> 0), hprf (ih `at` Inst @"n" (n-1))]
                                       =: map f (drop (n - 1) xs)
                                       ?? [hyp (n .> 0), hprf (dcA `at` (Inst @"n" n, Inst @"x" x, Inst @"xs" xs))]
                                       =: map f (drop n (x .: xs))
                                       =: qed

   -- I'm a bit surprised that z3 can't deduce the following with a simple-lemma, which is essentially a simple case-split.
   -- But the good thing about calc is that it lets us direct the tool in precise ways that we'd like.
   calc "drop_map"
        (\(Forall @"xs" xs) (Forall @"n" n) -> drop n (map f xs) .== map f (drop n xs)) $
        \xs n -> [] |- let result = drop n (map f xs) .== map f (drop n xs)
                    in result
                    =: ite (n .<= 0) (n .<= 0 .=> result) (n .> 0 .=> result) ?? h1
                    =: ite (n .<= 0) sTrue                (n .> 0 .=> result) ?? h2
                    =: ite (n .<= 0) sTrue                sTrue
                    =: sTrue
                    =: qed

-- | @n >= 0 ==> length (take n xs) = length xs \`min\` n@
--
-- >>> length_take
-- Lemma: length_take                      Q.E.D.
-- [Proven] length_take
length_take :: IO Proof
length_take = runKD $
     lemma "length_take"
           (\(Forall @"n" n) (Forall @"xs" (xs :: SList A)) -> n .>= 0 .=> length (take n xs) .== length xs `smin` n)
           []

-- | @n >= 0 ==> length (drop n xs) = (length xs - n) \`max\` 0@
--
-- >>> length_drop
-- Lemma: length_drop                      Q.E.D.
-- [Proven] length_drop
length_drop :: IO Proof
length_drop = runKD $
     lemma "length_drop"
           (\(Forall @"n" n) (Forall @"xs" (xs :: SList A)) -> n .>= 0 .=> length (drop n xs) .== (length xs - n) `smax` 0)
           []

-- | @length xs \<= n ==\> take n xs == xs@
--
-- >>> take_all
-- Lemma: take_all                         Q.E.D.
-- [Proven] take_all
take_all :: IO Proof
take_all = runKD $
    lemma "take_all"
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList A)) -> length xs .<= n .=> take n xs .== xs)
          []

-- | @length xs \<= n ==\> drop n xs == nil@
--
-- >>> drop_all
-- Lemma: drop_all                         Q.E.D.
-- [Proven] drop_all
drop_all :: IO Proof
drop_all = runKD $
    lemma "drop_all"
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList A)) -> length xs .<= n .=> drop n xs .== nil)
          []

-- | @take n (xs ++ ys) = (take n xs ++ take (n - length xs) ys)@
--
-- >>> take_append
-- Lemma: take_append
--   Step  : 1                             Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] take_append
take_append :: IO Proof
take_append = runKD $
    calc "take_append"
         (\(Forall @"n" n) (Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> take n (xs ++ ys) .== take n xs ++ take (n - length xs) ys) $

         -- z3 requires an explicit split here on xs. cvc5 actually proves this out-of-the-box without any helping steps.
         \n (xs :: SList A) ys -> [] |- take n (xs ++ ys)
                                     ?? "case split on xs"
                                     =: ite (null xs)
                                            (take n ys)
                                            (take n (head xs .: (tail xs ++ ys)))
                                     =: qed

-- | @drop n (xs ++ ys) = drop n xs ++ drop (n - length xs) ys@
--
-- NB. As of Feb 2025, z3 struggles to prove this, but cvc5 gets it out-of-the-box.
--
-- >>> drop_append
-- Lemma: drop_append                      Q.E.D.
-- [Proven] drop_append
drop_append :: IO Proof
drop_append = runKD $
    lemmaWith cvc5 "drop_append"
                   (\(Forall @"n" n) (Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> drop n (xs ++ ys) .== drop n xs ++ drop (n - length xs) ys)
                   []

-- * Summing via halving

-- | We prove that summing a list can be done by halving the list, summing parts, and adding the results. The proof uses
-- strong induction. We have:
--
-- >>> sumHalves
-- Inductive lemma: sumAppend
--   Base: sumAppend.Base                  Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: sumAppend.Step                  Q.E.D.
-- Inductive lemma (strong): sumHalves
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: sumHalves.Step                  Q.E.D.
-- [Proven] sumHalves
sumHalves :: IO Proof
sumHalves = runKD $ do

    let halvingSum :: SList Integer -> SInteger
        halvingSum = smtFunction "halvingSum" $ \xs -> ite (null xs .|| null (tail xs))
                                                           (sum xs)
                                                           (let (f, s) = splitAt (length xs `sDiv` 2) xs
                                                            in halvingSum f + halvingSum s)

        sum :: SList Integer -> SInteger
        sum = smtFunction "sum" $ \xs -> ite (null xs) 0 (head xs + sum (tail xs))

    helper <- induct "sumAppend"
                     (\(Forall @"xs" xs) (Forall @"ys" ys) -> sum (xs ++ ys) .== sum xs + sum ys) $
                     \ih x xs ys -> [] |- sum (x .: xs ++ ys)
                                       =: x + sum (xs ++ ys)
                                       ?? ih
                                       =: x + sum xs + sum ys
                                       =: sum (x .: xs) + sum ys
                                       =: qed

    -- Use strong induction to prove the theorem. CVC5 solves this with ease, but z3 struggles.
    error "need to fix this" halvingSum helper
    {-
    sInductWith cvc5 "sumHalves"
                (\(Forall @"xs" xs) -> halvingSum xs .== sum xs) $
                \ih x xs -> [] |- halvingSum (x .: xs)
                               =: let (f, s) = splitAt (length (x .: xs) `sDiv` 2) (x .: xs)
                                  in halvingSum f + halvingSum s
                               ?? ih `at` Inst @"xs" f
                               =: sum f + halvingSum s
                               ?? ih `at` Inst @"xs" s
                               =: sum f + sum s
                               ?? helper `at` (Inst @"xs" f, Inst @"ys" s)
                               =: sum (f ++ s)
                               ?? "simplify"
                               =: sum (x .: xs)
                               =: qed
                               -}

-- * Zip

-- | @length xs = length ys ⟹ map fst (zip xs ys) = xs@
--
-- >>> map_fst_zip
-- Inductive lemma: map_fst_zip
--   Base: map_fst_zip.Base                Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: map_fst_zip.Step                Q.E.D.
-- [Proven] map_fst_zip
map_fst_zip :: IO Proof
map_fst_zip = runKD $
   induct "map_fst_zip"
          (\(Forall @"xs" (xs :: SList A), Forall @"ys" (ys :: SList B)) -> length xs .== length ys .=> map fst (zip xs ys) .== xs) $
          \ih (x :: SA, xs, y :: SB, ys) -> [length (x .: xs) .== length (y .: ys)]
                                         |- map fst (zip (x .: xs) (y .: ys))
                                         =: map fst (tuple (x, y) .: zip xs ys)
                                         =: fst (tuple (x, y)) .: map fst (zip xs ys)
                                         =: x .: map fst (zip xs ys)
                                         ?? [hprf ih, hyp (length xs .== length ys)]
                                         =: x .: xs
                                         =: qed

-- | @length xs = length ys ⟹ map snd (zip xs ys) = xs@
--
-- >>> map_snd_zip
-- Inductive lemma: map_snd_zip
--   Base: map_snd_zip.Base                Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: map_snd_zip.Step                Q.E.D.
-- [Proven] map_snd_zip
map_snd_zip :: IO Proof
map_snd_zip = runKD $
   induct "map_snd_zip"
          (\(Forall @"xs" (xs :: SList A), Forall @"ys" (ys :: SList B)) -> length xs .== length ys .=> map snd (zip xs ys) .== ys) $
          \ih (x :: SA, xs, y :: SB, ys) -> [length (x .: xs) .== length (y .: ys)]
                                         |- map snd (zip (x .: xs) (y .: ys))
                                         =: map snd (tuple (x, y) .: zip xs ys)
                                         =: snd (tuple (x, y)) .: map snd (zip xs ys)
                                         =: y .: map snd (zip xs ys)
                                         ?? [hprf ih, hyp (length xs .== length ys)]
                                         =: y .: ys
                                         =: qed

-- | @map fst (zip xs ys) = take (min (length xs) (length ys)) xs@
--
-- >>> map_fst_zip_take
-- Lemma: take_cons                        Q.E.D.
-- Inductive lemma: map_fst_zip_take
--   Base: map_fst_zip_take.Base           Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: map_fst_zip_take.Step           Q.E.D.
-- [Proven] map_fst_zip_take
map_fst_zip_take :: IO Proof
map_fst_zip_take = runKD $ do
   tc <- use take_cons

   induct "map_fst_zip_take"
          (\(Forall @"xs" (xs :: SList A), Forall @"ys" (ys :: SList B)) -> map fst (zip xs ys) .== take (length xs `smin` length ys) xs) $
          \ih (x :: SA, xs, y :: SB, ys) -> []
                                         |- map fst (zip (x .: xs) (y .: ys))
                                         =: map fst (tuple (x, y) .: zip xs ys)
                                         =: x .: map fst (zip xs ys)
                                         ?? ih
                                         =: x .: take (length xs `smin` length ys) xs
                                         ?? tc
                                         =: take (1 + (length xs `smin` length ys)) (x .: xs)
                                         =: take (length (x .: xs) `smin` length (y .: ys)) (x .: xs)
                                         =: qed

-- | @map snd (zip xs ys) = take (min (length xs) (length ys)) xs@
--
-- >>> map_snd_zip_take
-- Lemma: take_cons                        Q.E.D.
-- Inductive lemma: map_snd_zip_take
--   Base: map_snd_zip_take.Base           Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: map_snd_zip_take.Step           Q.E.D.
-- [Proven] map_snd_zip_take
map_snd_zip_take :: IO Proof
map_snd_zip_take = runKD $ do
   tc <- use take_cons

   induct "map_snd_zip_take"
          (\(Forall @"xs" (xs :: SList A), Forall @"ys" (ys :: SList B)) -> map snd (zip xs ys) .== take (length xs `smin` length ys) ys) $
          \ih (x :: SA, xs, y :: SB, ys) -> []
                                         |- map snd (zip (x .: xs) (y .: ys))
                                         =: map snd (tuple (x, y) .: zip xs ys)
                                         =: y .: map snd (zip xs ys)
                                         ?? ih
                                         =: y .: take (length xs `smin` length ys) ys
                                         ?? tc
                                         =: take (1 + (length xs `smin` length ys)) (y .: ys)
                                         =: take (length (x .: xs) `smin` length (y .: ys)) (y .: ys)
                                         =: qed

{- HLint ignore reverseReverse "Redundant reverse" -}
{- HLint ignore allAny         "Use and"           -}
{- HLint ignore foldrMapFusion "Fuse foldr/map"    -}
{- HLint ignore filterConcat   "Move filter"       -}
{- HLint ignore module         "Use camelCase"     -}
{- HLint ignore module         "Use first"         -}
{- HLint ignore module         "Use second"        -}
{- HLint ignore module         "Use zipWith"       -}
