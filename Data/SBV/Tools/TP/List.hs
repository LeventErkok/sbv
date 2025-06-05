-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.TP.List
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A variety of TP proofs on list processing functions. Note that
-- these proofs only hold for finite lists. SMT-solvers do not model infinite
-- lists, and hence all claims are for finite (but arbitrary-length) lists.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.TP.List (
     -- * Append
     appendNull, consApp, appendAssoc, initsLength, tailsLength, tailsAppend

     -- * Reverse
   , revLen, revApp, revCons, revSnoc, revRev

     -- * Length
   , lengthTail, lenAppend, lenAppend2

     -- * Replicate
   , replicateLength

     -- * All and any
   , allAny

     -- * Map
   , mapEquiv, mapAppend, mapReverse, mapCompose

     -- * Foldr and foldl
   , foldrMapFusion, foldrFusion, foldrOverAppend, foldlOverAppend, foldrFoldlDuality, foldrFoldlDualityGeneralized, foldrFoldl
   , bookKeeping

     -- * Filter
   , filterAppend, filterConcat

     -- * Difference
   , appendDiff, diffAppend, diffDiff

     -- * Partition
   , partition1, partition2

    -- * Take and drop
   , take_take, drop_drop, take_drop, take_cons, take_map, drop_cons, drop_map, length_take, length_drop, take_all, drop_all
   , take_append, drop_append

   -- * Zip
   , map_fst_zip
   , map_snd_zip
   , map_fst_zip_take
   , map_snd_zip_take

   -- * Counting elements
   , count, countAppend, takeDropCount, countNonNeg, countElem, elemCount

   -- * Disjointness
   , disjoint, disjointDiff

   -- * Interleaving
   , interleave, uninterleave, interleaveLen, interleaveRoundTrip
 ) where

import Prelude (Eq, ($), Num(..), id, (.), flip)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.Tools.TP

import Data.Proxy

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.SBV.Tools.TP
-- >>> import Data.Proxy
-- >>> import Control.Exception
#endif

-- | @xs ++ [] == xs@
--
-- >>> runTP $ appendNull (Proxy @Integer)
-- Lemma: appendNull @Integer              Q.E.D.
-- [Proven] appendNull @Integer
appendNull :: forall a. SymVal a => Proxy a -> TP Proof
appendNull p = lemma (atProxy p "appendNull")
                     (\(Forall @"xs" (xs :: SList a)) -> xs ++ nil .== xs)
                     []

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- >>> runTP $ consApp (Proxy @Integer)
-- Lemma: consApp @Integer                 Q.E.D.
-- [Proven] consApp @Integer
consApp :: forall a. SymVal a => Proxy a -> TP Proof
consApp p = lemma (atProxy p "consApp")
                  (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys))
                  []

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- >>> runTP $ appendAssoc (Proxy @Integer)
-- Lemma: appendAssoc @Integer             Q.E.D.
-- [Proven] appendAssoc @Integer
--
-- Surprisingly, z3 can prove this without any induction. (Since SBV's append translates directly to
-- the concatenation of sequences in SMTLib, it must trigger an internal heuristic in z3
-- that proves it right out-of-the-box!)
appendAssoc :: forall a. SymVal a => Proxy a -> TP Proof
appendAssoc p =
   lemma (atProxy p "appendAssoc")
         (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) (Forall @"zs" zs) -> xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs)
         []

-- | @length (inits xs) == 1 + length xs@
--
-- >>> runTP $ initsLength (Proxy @Integer)
-- Inductive lemma (strong): initsLength @Integer
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] initsLength @Integer
initsLength :: forall a. SymVal a => Proxy a -> TP Proof
initsLength p =
   sInduct (atProxy p "initsLength")
           (\(Forall @"xs" (xs :: SList a)) -> length (inits xs) .== 1 + length xs)
           (length @a) $
           \ih (xs :: SList a) -> [] |- length (inits xs)
                                     ?? ih
                                     =: 1 + length xs
                                     =: qed

-- | @length (tails xs) == 1 + length xs@
--
-- >>> runTP $ tailsLength (Proxy @Integer)
-- Inductive lemma: tailsLength @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] tailsLength @Integer
tailsLength :: forall a. SymVal a => Proxy a -> TP Proof
tailsLength p =
   induct (atProxy p "tailsLength")
          (\(Forall @"xs" (xs :: SList a)) -> length (tails xs) .== 1 + length xs) $
          \ih (x :: SBV a) xs -> [] |- length (tails (x .: xs))
                                    =: length (tails xs ++ singleton (x .: xs))
                                    =: length (tails xs) + 1
                                    ?? ih
                                    =: 1 + length xs + 1
                                    =: 1 + length (x .: xs)
                                    =: qed

-- | @tails (xs ++ ys) == map (++ ys) (tails xs) ++ tail (tails ys)@
--
-- This property comes from Richard Bird's "Pearls of functional Algorithm Design" book, chapter 2.
-- Note that it is not exactly as stated there, as the definition of @tail@ Bird uses is different
-- than the standard Haskell function @tails@: Bird's version does not return the empty list as the
-- tail. So, we slightly modify it to fit the standard definition.
--
-- >>> runTP $ tailsAppend (Proxy @Integer)
-- Inductive lemma: base case
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: helper
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: tailsAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] tailsAppend @Integer
tailsAppend :: forall a. SymVal a => Proxy a -> TP Proof
tailsAppend p = do

   let -- Would like to define appendEach like this:
       --
       --       appendEach xs ys = map (++ ys) xs
       --
       -- But capture of ys is not allowed by SBV.  So we use an
       -- explicit recursive definition to pass around ys.
       appendEach :: SList [a] -> SList a -> SList [a]
       appendEach = smtFunction "appendEach" $ \xs ys -> ite (null xs)
                                                             nil
                                                             ((head xs ++ ys) .: appendEach (tail xs) ys)

   -- Even proving the base case of induction is hard due to recursive definition. So we first prove the base case by induction.
   bc <- induct "base case"
                (\(Forall @"ys" (ys :: SList a)) -> tails ys .== singleton ys ++ tail (tails ys)) $
                \ih (y :: SBV a) ys ->
                   [] |- tails (y .: ys)
                      =: singleton (y .: ys) ++ tails ys
                      ?? ih
                      =: singleton (y .: ys) ++ singleton ys ++ tail (tails ys)
                      =: singleton (y .: ys) ++ tail (tails (y .: ys))
                      =: qed

   -- Also need a helper to relate how appendEach and tails work together
   helper <- calc "helper"
                   (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"x" x) ->
                        appendEach (tails (x .: xs)) ys .== singleton ((x .: xs) ++ ys) ++ appendEach (tails xs) ys) $
                   \xs ys x -> [] |- appendEach (tails (x .: xs)) ys
                                  =: appendEach (singleton (x .: xs) ++ tails xs) ys
                                  =: singleton ((x .: xs) ++ ys) ++ appendEach (tails xs) ys
                                  =: qed

   induct (atProxy p "tailsAppend")
          (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> tails (xs ++ ys) .== appendEach (tails xs) ys ++ tail (tails ys)) $
          \ih (x :: SBV a) xs ys ->
                [getProof bc]
             |- tails ((x .: xs) ++ ys)
             =: tails (x .: (xs ++ ys))
             =: singleton (x .: (xs ++ ys)) ++ tails (xs ++ ys)
             ?? ih
             =: singleton ((x .: xs) ++ ys) ++ appendEach (tails xs) ys ++ tail (tails ys)
             ?? helper
             =: appendEach (tails (x .: xs)) ys ++ tail (tails ys)
             =: qed

-- | @length xs == length (reverse xs)@
--
-- >>> runTP $ revLen (Proxy @Integer)
-- Inductive lemma: revLen @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revLen @Integer
revLen :: forall a. SymVal a => Proxy a -> TP Proof
revLen p =
   induct (atProxy p "revLen")
          (\(Forall @"xs" (xs :: SList a)) -> length (reverse xs) .== length xs) $
          \ih (x :: SBV a) xs -> [] |- length (reverse (x .: xs))
                                    =: length (reverse xs ++ singleton x)
                                    =: length (reverse xs) + length (singleton x)
                                    ?? ih
                                    =: length xs + 1
                                    =: length (x .: xs)
                                    =: qed

-- | @reverse (xs ++ ys) .== reverse ys ++ reverse xs@
--
-- >>> runTP $ revApp (Proxy @Integer)
-- Inductive lemma: revApp @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revApp @Integer
revApp :: forall a. SymVal a => Proxy a -> TP Proof
revApp p =
   induct (atProxy p "revApp")
          (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> reverse (xs ++ ys) .== reverse ys ++ reverse xs) $
          \ih (x :: SBV a) xs ys -> [] |- reverse ((x .: xs) ++ ys)
                                       =: reverse (x .: (xs ++ ys))
                                       =: reverse (xs ++ ys) ++ singleton x
                                       ?? ih
                                       =: (reverse ys ++ reverse xs) ++ singleton x
                                       =: reverse ys ++ (reverse xs ++ singleton x)
                                       =: reverse ys ++ reverse (x .: xs)
                                       =: qed

-- | @reverse (x:xs) == reverse xs ++ [x]@
--
-- >>> runTP $ revCons (Proxy @Integer)
-- Lemma: revCons @Integer                 Q.E.D.
-- [Proven] revCons @Integer
revCons :: forall a. SymVal a => Proxy a -> TP Proof
revCons p = lemma (atProxy p "revCons")
                  (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) -> reverse (x .: xs) .== reverse xs ++ singleton x)
                  []

-- | @reverse (xs ++ [x]) == x : reverse xs@
--
-- >>> runTP $ revSnoc (Proxy @Integer)
-- Inductive lemma: revApp @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: revSnoc @Integer                 Q.E.D.
-- [Proven] revSnoc @Integer
revSnoc :: forall a. SymVal a => Proxy a -> TP Proof
revSnoc p = do
   ra <- revApp p

   lemma (atProxy p "revSnoc")
         (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) -> reverse (xs ++ singleton x) .== x .: reverse xs)
         [ra]

-- | @reverse (reverse xs) == xs@
--
-- >>> runTP $ revRev (Proxy @Integer)
-- Inductive lemma: revApp @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revRev @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revRev @Integer
revRev :: forall a. SymVal a => Proxy a -> TP Proof
revRev p = do

   ra <- revApp p

   induct (atProxy p "revRev")
          (\(Forall @"xs" (xs :: SList a)) -> reverse (reverse xs) .== xs) $
          \ih (x :: SBV a) xs -> [] |- reverse (reverse (x .: xs))
                                    =: reverse (reverse xs ++ singleton x)           ?? ra
                                    =: reverse (singleton x) ++ reverse (reverse xs) ?? ih
                                    =: singleton x ++ xs
                                    =: x .: xs
                                    =: qed

-- | @length (x : xs) == 1 + length xs@
--
-- >>> runTP $ lengthTail (Proxy @Integer)
-- Lemma: lengthTail @Integer              Q.E.D.
-- [Proven] lengthTail @Integer
lengthTail :: forall a. SymVal a => Proxy a -> TP Proof
lengthTail p =
   lemma (atProxy p "lengthTail")
         (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) -> length (x .: xs) .== 1 + length xs)
         []

-- | @length (xs ++ ys) == length xs + length ys@
--
-- >>> runTP $ lenAppend (Proxy @Integer)
-- Lemma: lenAppend @Integer               Q.E.D.
-- [Proven] lenAppend @Integer
lenAppend :: forall a. SymVal a => Proxy a -> TP Proof
lenAppend p =
   lemma (atProxy p "lenAppend")
         (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> length (xs ++ ys) .== length xs + length ys)
         []

-- | @length xs == length ys -> length (xs ++ ys) == 2 * length xs@
--
-- >>> runTP $ lenAppend2 (Proxy @Integer)
-- Lemma: lenAppend2 @Integer              Q.E.D.
-- [Proven] lenAppend2 @Integer
lenAppend2 :: forall a. SymVal a => Proxy a -> TP Proof
lenAppend2 p =
    lemma (atProxy p "lenAppend2")
          (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> length xs .== length ys .=> length (xs ++ ys) .== 2 * length xs)
          []

-- | @length (replicate k x) == max (0, k)@
--
-- >>> runTP $ replicateLength (Proxy @Integer)
-- Inductive lemma: replicateLength @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] replicateLength @Integer
replicateLength :: forall a. SymVal a => Proxy a -> TP Proof
replicateLength p =
   induct (atProxy p "replicateLength")
          (\(Forall @"k" k) (Forall @"x" (x :: SBV a)) -> length (replicate k x) .== 0 `smax` k) $
          \ih k (x :: SBV a) -> [] |- length (replicate (k+1) x)
                             =: cases [ k .< 0  ==> trivial
                                      , k .>= 0 ==> length (x .: replicate k x)
                                                 =: 1 + length (replicate k x)
                                                 ?? ih
                                                 =: 1 + 0 `smax` k
                                                 =: 0 `smax` (k+1)
                                                 =: qed
                                      ]

-- | @not (all id xs) == any not xs@
--
-- A list of booleans is not all true, if any of them is false.
--
-- >>> runTP allAny
-- Inductive lemma: allAny
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] allAny
allAny :: TP Proof
allAny = induct "allAny"
                (\(Forall @"xs" xs) -> sNot (all id xs) .== any sNot xs) $
                \ih x xs -> [] |- sNot (all id (x .: xs))
                               =: sNot (x .&& all id xs)
                               =: (sNot x .|| sNot (all id xs))
                               ?? ih
                               =: sNot x .|| any sNot xs
                               =: any sNot (x .: xs)
                               =: qed

-- | @f == g ==> map f xs == map g xs@
--
-- >>> runTP $ mapEquiv @Integer @Integer (uninterpret "f") (uninterpret "g")
-- Inductive lemma: mapEquiv @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapEquiv @(Integer,Integer)
mapEquiv :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> (SBV a -> SBV b) -> TP Proof
mapEquiv f g = do
   let f'eq'g :: SBool
       f'eq'g = quantifiedBool $ \(Forall @"x" x) -> f x .== g x

   induct (atProxy (Proxy @(a, b)) "mapEquiv")
          (\(Forall @"xs" xs) -> f'eq'g .=> map f xs .== map g xs) $
          \ih x xs -> [f'eq'g] |- map f (x .: xs) .== map g (x .: xs)
                               =: f x .: map f xs .== g x .: map g xs
                               =: f x .: map f xs .== f x .: map g xs
                               ?? ih
                               =: f x .: map f xs .== f x .: map f xs
                               =: map f (x .: xs) .== map f (x .: xs)
                               =: qed

-- | @map f (xs ++ ys) == map f xs ++ map f ys@
--
-- >>> runTP $ mapAppend @Integer @Integer (uninterpret "f")
-- Inductive lemma: mapAppend @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapAppend @(Integer,Integer)
mapAppend :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP Proof
mapAppend f =
   induct (atProxy (Proxy @(a, b)) "mapAppend")
          (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> map f (xs ++ ys) .== map f xs ++ map f ys) $
          \ih x xs ys -> [] |- map f ((x .: xs) ++ ys)
                            =: map f (x .: (xs ++ ys))
                            =: f x .: map f (xs ++ ys)
                            ?? ih
                            =: f x .: (map f xs  ++ map f ys)
                            =: (f x .: map f xs) ++ map f ys
                            =: map f (x .: xs) ++ map f ys
                            =: qed

-- | @map f . reverse == reverse . map f@
--
-- >>> runTP $ mapReverse @Integer @String (uninterpret "f")
-- Inductive lemma: mapAppend @(Integer,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: mapReverse @(Integer,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapReverse @(Integer,[Char])
mapReverse :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP Proof
mapReverse f = do
     mApp <- mapAppend f

     induct (atProxy (Proxy @(a, b)) "mapReverse")
            (\(Forall @"xs" xs) -> reverse (map f xs) .== map f (reverse xs)) $
            \ih x xs -> [] |- reverse (map f (x .: xs))
                           =: reverse (f x .: map f xs)
                           =: reverse (map f xs) ++ singleton (f x)
                           ?? ih
                           =: map f (reverse xs) ++ singleton (f x)
                           =: map f (reverse xs) ++ map f (singleton x)
                           ?? mApp
                           =: map f (reverse xs ++ singleton x)
                           =: map f (reverse (x .: xs))
                           =: qed

-- | @map f . map g == map (f . g)@
--
-- >>> runTP $ mapCompose @Integer @Bool @String (uninterpret "f") (uninterpret "g")
-- Inductive lemma: mapCompose @(Integer,Bool,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapCompose @(Integer,Bool,[Char])
mapCompose :: forall a b c. (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b) -> (SBV b -> SBV c) -> TP Proof
mapCompose f g =
  induct (atProxy (Proxy @(a, b, c)) "mapCompose")
         (\(Forall @"xs" (xs :: SList a)) -> map g (map f xs) .== map (g . f) xs) $
         \ih x xs -> [] |- map g (map f (x .: xs))
                        =: map g (f x .: map f xs)
                        =: g (f x) .: map g (map f xs)
                        ?? ih
                        =: (g . f) x .: map (g . f) xs
                        =: map (g . f) (x .: xs)
                        =: qed

-- | @foldr f a . map g == foldr (f . g) a@
--
-- >>> runTP $ foldrMapFusion @Integer @Bool @String (uninterpret "a") (uninterpret "b") (uninterpret "c")
-- Inductive lemma: foldrMapFusion @(Integer,Bool,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrMapFusion @(Integer,Bool,[Char])
foldrMapFusion :: forall a b c. (SymVal a, SymVal b, SymVal c) => SBV a -> (SBV c -> SBV b) -> (SBV b -> SBV a -> SBV a) -> TP Proof
foldrMapFusion a g f =
  induct (atProxy (Proxy @(a, b, c)) "foldrMapFusion")
         (\(Forall @"xs" xs) -> foldr f a (map g xs) .== foldr (f . g) a xs) $
         \ih x xs -> [] |- foldr f a (map g (x .: xs))
                        =: foldr f a (g x .: map g xs)
                        =: g x `f` foldr f a (map g xs) ?? ih
                        =: g x `f` foldr (f . g) a xs
                        =: foldr (f . g) a (x .: xs)
                        =: qed

-- |
--
-- @
--   f . foldr g a == foldr h b
--   provided, f a = b and for all x and y, f (g x y) == h x (f y).
-- @
--
-- >>> runTP $ foldrFusion @Integer @Bool @String (uninterpret "a") (uninterpret "b") (uninterpret "f") (uninterpret "g") (uninterpret "h")
-- Inductive lemma: foldrFusion @(Integer,Bool,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFusion @(Integer,Bool,[Char])
foldrFusion :: forall a b c. (SymVal a, SymVal b, SymVal c) => SBV a -> SBV b -> (SBV a -> SBV b) -> (SBV c -> SBV a -> SBV a) -> (SBV c -> SBV b -> SBV b) -> TP Proof
foldrFusion a b f g h = do
   let -- Assumptions under which the equality holds
       h1 = f a .== b
       h2 = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) -> f (g x y) .== h x (f y)

   induct (atProxy (Proxy @(a, b, c)) "foldrFusion")
          (\(Forall @"xs" xs) -> h1 .&& h2 .=> f (foldr g a xs) .== foldr h b xs) $
          \ih x xs -> [h1, h2] |- f (foldr g a (x .: xs))
                               =: f (g x (foldr g a xs))
                               =: h x (f (foldr g a xs))  ?? ih
                               =: h x (foldr h b xs)
                               =: foldr h b (x .: xs)
                               =: qed

-- | @foldr f a (xs ++ ys) == foldr f (foldr f a ys) xs@
--
-- >>> runTP $ foldrOverAppend @Integer (uninterpret "a") (uninterpret "f")
-- Inductive lemma: foldrOverAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrOverAppend @Integer
foldrOverAppend :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> TP Proof
foldrOverAppend a f =
   induct (atProxy (Proxy @a) "foldrOverAppend")
          (\(Forall @"xs" xs) (Forall @"ys" ys) -> foldr f a (xs ++ ys) .== foldr f (foldr f a ys) xs) $
          \ih x xs ys -> [] |- foldr f a ((x .: xs) ++ ys)
                            =: foldr f a (x .: (xs ++ ys))
                            =: x `f` foldr f a (xs ++ ys)       ?? ih
                            =: x `f` foldr f (foldr f a ys) xs
                            =: foldr f (foldr f a ys) (x .: xs)
                            =: qed

-- | @foldl f a (xs ++ ys) == foldl f (foldl f a xs) ys@
--
-- >>> runTP $ foldlOverAppend @Integer @Bool (uninterpret "f")
-- Inductive lemma: foldlOverAppend @(Integer,Bool)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldlOverAppend @(Integer,Bool)
foldlOverAppend :: forall a b. (SymVal a, SymVal b) => (SBV b -> SBV a -> SBV b) -> TP Proof
foldlOverAppend f =
   induct (atProxy (Proxy @(a, b)) "foldlOverAppend")
          (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"a" a) -> foldl f a (xs ++ ys) .== foldl f (foldl f a xs) ys) $
          \ih x xs ys a -> [] |- foldl f a ((x .: xs) ++ ys)
                              =: foldl f a (x .: (xs ++ ys))
                              =: foldl f (a `f` x) (xs ++ ys)
                              -- z3 is smart enough to instantiate the IH correctly below, but we're
                              -- using an explicit instantiation to be clear about the use of @a@ at a different value
                              ?? ih `at` (Inst @"ys" ys, Inst @"a" (a `f` x))
                              =: foldl f (foldl f (a `f` x) xs) ys
                              =: qed

-- | @foldr f e xs == foldl (flip f) e (reverse xs)@
--
-- >>> runTP $ foldrFoldlDuality @Integer @String (uninterpret "f")
-- Inductive lemma: foldlOverAppend @(Integer,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrFoldlDuality @(Integer,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFoldlDuality @(Integer,[Char])
foldrFoldlDuality :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> TP Proof
foldrFoldlDuality f = do
   foa <- foldlOverAppend (flip f)

   induct (atProxy (Proxy @(a, b)) "foldrFoldlDuality")
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

-- | Given:
--
-- @
--     x \@ (y \@ z) = (x \@ y) \@ z     (associativity of @)
-- and e \@ x = x                     (left unit)
-- and x \@ e = x                     (right unit)
-- @
--
-- Proves:
--
-- @
--     foldr (\@) e xs == foldl (\@) e xs
-- @
--
-- >>> runTP $ foldrFoldlDualityGeneralized @Integer (uninterpret "e") (uninterpret "|@|")
-- Inductive lemma: helper @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrFoldlDuality @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFoldlDuality @Integer
foldrFoldlDualityGeneralized :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> TP Proof
foldrFoldlDualityGeneralized  e (@) = do
   -- Assumptions under which the equality holds
   let assoc = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x @ (y @ z) .== (x @ y) @ z
       lunit = quantifiedBool $ \(Forall @"x" x) -> e @ x .== x
       runit = quantifiedBool $ \(Forall @"x" x) -> x @ e .== x

   -- Helper: foldl (@) (y @ z) xs = y @ foldl (@) z xs
   -- Note the instantiation of the IH at a different value for z. It turns out
   -- we don't have to actually specify this since z3 can figure it out by itself, but we're being explicit.
   helper <- induct (atProxy (Proxy @a) "helper")
                    (\(Forall @"xs" xs) (Forall @"y" y) (Forall @"z" z) -> assoc .=> foldl (@) (y @ z) xs .== y @ foldl (@) z xs) $
                    \ih x xs y z -> [assoc] |- foldl (@) (y @ z) (x .: xs)
                                            =: foldl (@) ((y @ z) @ x) xs
                                            ?? assoc
                                            =: foldl (@) (y @ (z @ x)) xs
                                            ?? ih `at` (Inst @"y" y, Inst @"z" (z @ x))
                                            =: y @ foldl (@) (z @ x) xs
                                            =: y @ foldl (@) z (x .: xs)
                                            =: qed

   induct (atProxy (Proxy @a) "foldrFoldlDuality")
          (\(Forall @"xs" xs) -> assoc .&& lunit .&& runit .=> foldr (@) e xs .== foldl (@) e xs) $
          \ih x xs -> [assoc, lunit, runit] |- foldr (@) e (x .: xs)
                                            =: x @ foldr (@) e xs    ?? ih
                                            =: x @ foldl (@) e xs    ?? helper
                                            =: foldl (@) (x @ e) xs  ?? runit
                                            =: foldl (@) x xs        ?? lunit
                                            =: foldl (@) (e @ x) xs
                                            =: foldl (@) e (x .: xs)
                                            =: qed

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
-- In Bird's Introduction to Functional Programming book (2nd edition) this is called the second duality theorem:
--
-- >>> runTP $ foldrFoldl @Integer @String (uninterpret "<+>") (uninterpret "<*>") (uninterpret "e")
-- Inductive lemma: foldl over <*>/<+> @(Integer,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrFoldl @(Integer,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFoldl @(Integer,[Char])
foldrFoldl :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> (SBV b -> SBV a -> SBV b) -> SBV b-> TP Proof
foldrFoldl (<+>) (<*>) e = do
   -- Assumptions about the operators
   let -- (x <+> y) <*> z == x <+> (y <*> z)
       assoc = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> (x <+> y) <*> z .== x <+> (y <*> z)

       -- x <+> e == e <*> x
       unit  = quantifiedBool $ \(Forall @"x" x) -> x <+> e .== e <*> x

   -- Helper: x <+> foldl (<*>) y xs == foldl (<*>) (x <+> y) xs
   helper <-
      induct (atProxy (Proxy @(a, b)) "foldl over <*>/<+>")
             (\(Forall @"xs" xs) (Forall @"x" x) (Forall @"y" y) -> assoc .=> x <+> foldl (<*>) y xs .== foldl (<*>) (x <+> y) xs) $
             -- Using z to avoid confusion with the variable x already present, following Bird.
             -- z3 can figure out the proper instantiation of ih so the at call is unnecessary, but being explicit is helpful.
             \ih z xs x y -> [assoc] |- x <+> foldl (<*>) y (z .: xs)
                                     =: x <+> foldl (<*>) (y <*> z) xs    ?? ih `at` (Inst @"x" x, Inst @"y" (y <*> z))
                                     =: foldl (<*>) (x <+> (y <*> z)) xs  ?? assoc
                                     =: foldl (<*>) ((x <+> y) <*> z) xs
                                     =: foldl (<*>) (x <+> y) (z .: xs)
                                     =: qed

   -- Final proof:
   induct (atProxy (Proxy @(a, b)) "foldrFoldl")
          (\(Forall @"xs" xs) -> assoc .&& unit .=> foldr (<+>) e xs .== foldl (<*>) e xs) $
          \ih x xs -> [assoc, unit] |- foldr (<+>) e (x .: xs)
                                    =: x <+> foldr (<+>) e xs    ?? ih
                                    =: x <+> foldl (<*>) e xs    ?? helper
                                    =: foldl (<*>) (x <+> e) xs
                                    =: foldl (<*>) (e <*> x) xs
                                    =: foldl (<*>) e (x .: xs)
                                    =: qed

-- | Provided @f@ is associative and @a@ is its both left and right-unit:
--
-- @foldr f a . concat == foldr f a . map (foldr f a)@
--
-- >>> runTP $ bookKeeping @Integer (uninterpret "a") (uninterpret "f")
-- Inductive lemma: foldBase @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrOverAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: bookKeeping @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] bookKeeping @Integer
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
bookKeeping :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> TP Proof
bookKeeping a f = do

   -- Assumptions about f
   let assoc = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x `f` (y `f` z) .== (x `f` y) `f` z
       rUnit = quantifiedBool $ \(Forall @"x" x) -> x `f` a .== x
       lUnit = quantifiedBool $ \(Forall @"x" x) -> a `f` x .== x

   -- Helper: @foldr f y xs = foldr f a xs `f` y@
   helper <- induct (atProxy (Proxy @a) "foldBase")
                    (\(Forall @"xs" xs) (Forall @"y" y) -> lUnit .&& assoc .=> foldr f y xs .== foldr f a xs `f` y) $
                    \ih x xs y -> [lUnit, assoc] |- foldr f y (x .: xs)
                                                 =: x `f` foldr f y xs
                                                 ?? ih
                                                 =: x `f` (foldr f a xs `f` y)
                                                 =: (x `f` foldr f a xs) `f` y
                                                 =: foldr f a (x .: xs) `f` y
                                                 =: qed

   foa <- foldrOverAppend a f

   induct (atProxy (Proxy @a) "bookKeeping")
          (\(Forall @"xss" xss) -> assoc .&& rUnit .&& lUnit .=> foldr f a (concat xss) .== foldr f a (map (foldr f a) xss)) $
          \ih xs xss -> [assoc, rUnit, lUnit] |- foldr f a (concat (xs .: xss))
                                              =: foldr f a (xs ++ concat xss)
                                              ?? foa
                                              =: foldr f (foldr f a (concat xss)) xs
                                              ?? ih
                                              =: foldr f (foldr f a (map (foldr f a) xss)) xs
                                              ?? helper `at` (Inst @"xs" xs, Inst @"y" (foldr f a (map (foldr f a) xss)))
                                              =: foldr f a xs `f` foldr f a (map (foldr f a) xss)
                                              =: foldr f a (foldr f a xs .: map (foldr f a) xss)
                                              =: foldr f a (map (foldr f a) (xs .: xss))
                                              =: qed

-- | @filter p (xs ++ ys) == filter p xs ++ filter p ys@
--
-- >>> runTP $ filterAppend @Integer (uninterpret "p")
-- Inductive lemma: filterAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] filterAppend @Integer
filterAppend :: forall a. SymVal a => (SBV a -> SBool) -> TP Proof
filterAppend p =
   induct (atProxy (Proxy @a) "filterAppend")
          (\(Forall @"xs" xs) (Forall @"ys" ys) -> filter p xs ++ filter p ys .== filter p (xs ++ ys)) $
          \ih x xs ys -> [] |- filter p (x .: xs) ++ filter p ys
                            =: ite (p x) (x .: filter p xs) (filter p xs) ++ filter p ys
                            =: ite (p x) (x .: filter p xs ++ filter p ys) (filter p xs ++ filter p ys)
                            ?? ih
                            =: ite (p x) (x .: filter p (xs ++ ys)) (filter p (xs ++ ys))
                            =: filter p (x .: (xs ++ ys))
                            =: filter p ((x .: xs) ++ ys)
                            =: qed

-- | @filter p (concat xss) == concatMap (filter p xss)@
--
-- >>> runTP $ filterConcat @Integer (uninterpret "f")
-- Inductive lemma: filterAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: filterConcat @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] filterConcat @Integer
filterConcat :: forall a. SymVal a => (SBV a -> SBool) -> TP Proof
filterConcat p = do
  fa <- filterAppend p

  inductWith cvc5 (atProxy (Proxy @a) "filterConcat")
         (\(Forall @"xss" xss) -> filter p (concat xss) .== concatMap (filter p) xss) $
         \ih xs xss -> [] |- filter p (concat (xs .: xss))
                          =: filter p (xs ++ concat xss)
                          ?? fa
                          =: filter p xs ++ filter p (concat xss)
                          ?? ih
                          =: concatMap (filter p) (xs .: xss)
                          =: qed

-- | @(as ++ bs) \\ cs == (as \\ cs) ++ (bs \\ cs)@
--
-- >>> runTP $ appendDiff (Proxy @Integer)
-- Inductive lemma: appendDiff @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] appendDiff @Integer
appendDiff :: forall a. (Eq a, SymVal a) => Proxy a -> TP Proof
appendDiff p =
   induct (atProxy p "appendDiff")
          (\(Forall @"as" (as :: SList a)) (Forall @"bs" bs) (Forall @"cs" cs) -> (as ++ bs) \\ cs .== (as \\ cs) ++ (bs \\ cs)) $
          \ih (a :: SBV a) as bs cs ->
              [] |- (a .: as ++ bs) \\ cs
                 =: (a .: (as ++ bs)) \\ cs
                 =: ite (a `elem` cs) ((as ++ bs) \\ cs) (a .: ((as ++ bs) \\ cs))
                 ?? ih
                 =: ((a .: as) \\ cs) ++ (bs \\ cs)
                 =: qed

-- | @as \\ (bs ++ cs) == (as \\ bs) \\ cs@
--
-- >>> runTP $ diffAppend (Proxy @Integer)
-- Inductive lemma: diffAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] diffAppend @Integer
diffAppend :: forall a. (Eq a, SymVal a) => Proxy a -> TP Proof
diffAppend p =
   induct (atProxy p "diffAppend")
          (\(Forall @"as" (as :: SList a)) (Forall @"bs" bs) (Forall @"cs" cs) -> as \\ (bs ++ cs) .== (as \\ bs) \\ cs) $
          \ih (a :: SBV a) as bs cs ->
              [] |- (a .: as) \\ (bs ++ cs)
                 =: ite (a `elem` (bs ++ cs)) (as \\ (bs ++ cs)) (a .: (as \\ (bs ++ cs)))
                 ?? ih `at` (Inst @"bs" bs, Inst @"cs" cs)
                 =: ite (a `elem` (bs ++ cs)) ((as \\ bs) \\ cs) (a .: (as \\ (bs ++ cs)))
                 ?? ih `at` (Inst @"bs" bs, Inst @"cs" cs)
                 =: ite (a `elem` (bs ++ cs)) ((as \\ bs) \\ cs) (a .: ((as \\ bs) \\ cs))
                 =: ((a .: as) \\ bs) \\ cs
                 =: qed

-- | @(as \\ bs) \\ cs == (as \\ cs) \\ bs@
--
-- >>> runTP $ diffDiff (Proxy @Integer)
-- Inductive lemma: diffDiff @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.1.3 (2 way case split)
--       Step: 1.1.3.1                     Q.E.D.
--       Step: 1.1.3.2.1                   Q.E.D.
--       Step: 1.1.3.2.2 (a ∉ cs)          Q.E.D.
--       Step: 1.1.3.Completeness          Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                   Q.E.D.
--       Step: 1.2.2.1.2                   Q.E.D.
--       Step: 1.2.2.1.3 (a ∈ cs)          Q.E.D.
--       Step: 1.2.2.2.1                   Q.E.D.
--       Step: 1.2.2.2.2                   Q.E.D.
--       Step: 1.2.2.2.3 (a ∉ bs)          Q.E.D.
--       Step: 1.2.2.2.4 (a ∉ cs)          Q.E.D.
--       Step: 1.2.2.Completeness          Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] diffDiff @Integer
diffDiff :: forall a. (Eq a, SymVal a) => Proxy a -> TP Proof
diffDiff p =
   induct (atProxy p "diffDiff")
          (\(Forall @"as" (as :: SList a)) (Forall @"bs" bs) (Forall @"cs" cs) -> (as \\ bs) \\ cs .== (as \\ cs) \\ bs) $
          \ih (a :: SBV a) as bs cs ->
              [] |- ((a .: as) \\ bs) \\ cs
                 =: cases [ a `elem`    bs ==> (as \\ bs) \\ cs
                                            ?? ih
                                            =: (as \\ cs) \\ bs
                                            =: cases [ a `elem`    cs ==> ((a .: as) \\ cs) \\ bs
                                                                       =: qed
                                                     , a `notElem` cs ==> (a .: (as \\ cs)) \\ bs
                                                                       ?? "a ∉ cs"
                                                                       =: ((a .: as) \\ cs) \\ bs
                                                                       =: qed
                                                     ]
                          , a `notElem` bs ==> (a .: (as \\ bs)) \\ cs
                                            =: cases [ a `elem`    cs ==> (as \\ bs) \\ cs
                                                                       ?? ih
                                                                       =: (as \\ cs) \\ bs
                                                                       ?? "a ∈ cs"
                                                                       =: ((a .: as) \\ cs) \\ bs
                                                                       =: qed
                                                     , a `notElem` cs ==> a .: ((as \\ bs) \\ cs)
                                                                       ?? ih
                                                                       =: a .: ((as \\ cs) \\ bs)
                                                                       ?? "a ∉ bs"
                                                                       =: (a .: (as \\ cs)) \\ bs
                                                                       ?? "a ∉ cs"
                                                                       =: ((a .: as) \\ cs) \\ bs
                                                                       =: qed
                                                     ]
                          ]

-- | @disjoint as bs .=> as \\ bs == as@
--
-- >>> runTP $ disjointDiff (Proxy @Integer)
-- Inductive lemma: disjointDiff @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] disjointDiff @Integer
disjointDiff :: forall a. (Eq a, SymVal a) => Proxy a -> TP Proof
disjointDiff p =
   induct (atProxy p "disjointDiff")
          (\(Forall @"as" (as :: SList a)) (Forall @"bs" bs) -> disjoint as bs .=> as \\ bs .== as) $
          \ih (a :: SBV a) as bs -> [disjoint (a .: as) bs]
                                 |- (a .: as) \\ bs
                                 =: a .: (as \\ bs)
                                 ?? ih
                                 =: a .: as
                                 =: qed

-- | @fst (partition f xs) == filter f xs@
--
-- >>> runTP $ partition1 @Integer (uninterpret "f")
-- Inductive lemma: partition1 @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] partition1 @Integer
partition1 :: forall a. SymVal a => (SBV a -> SBool) -> TP Proof
partition1 f =
   induct (atProxy (Proxy @a) "partition1")
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
-- >>> runTP $ partition2 @Integer (uninterpret "f")
-- Inductive lemma: partition2 @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] partition2 @Integer
partition2 :: forall a. SymVal a => (SBV a -> SBool) -> TP Proof
partition2 f =
   induct (atProxy (Proxy @a) "partition2")
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

-- | @take n (take m xs) == take (n `smin` m) xs@
--
-- >>> runTP $ take_take (Proxy @Integer)
-- Lemma: take_take @Integer               Q.E.D.
-- [Proven] take_take @Integer
take_take :: forall a. SymVal a => Proxy a -> TP Proof
take_take p =
   lemma (atProxy p "take_take")
         (\(Forall @"xs" (xs :: SList a)) (Forall @"m" m) (Forall @"n" n) -> take n (take m xs) .== take (n `smin` m) xs)
         []


-- | @n >= 0 && m >= 0 ==> drop n (drop m xs) == drop (n + m) xs@
--
-- >>> runTP $ drop_drop (Proxy @Integer)
-- Lemma: drop_drop @Integer               Q.E.D.
-- [Proven] drop_drop @Integer
drop_drop :: forall a. SymVal a => Proxy a -> TP Proof
drop_drop p =
   lemma (atProxy p "drop_drop")
          (\(Forall @"n" n) (Forall @"m" m) (Forall @"xs" (xs :: SList a)) ->
                n .>= 0 .&& m .>= 0 .=> drop n (drop m xs) .== drop (n + m) xs)
          []

-- | @take n xs ++ drop n xs == xs@
--
-- >>> runTP $ take_drop (Proxy @Integer)
-- Lemma: take_drop @Integer               Q.E.D.
-- [Proven] take_drop @Integer
take_drop :: forall a. SymVal a => Proxy a -> TP Proof
take_drop p =
    lemma (atProxy p "take_drop")
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> take n xs ++ drop n xs .== xs)
          []

-- | @n .> 0 ==> take n (x .: xs) == x .: take (n - 1) xs@
--
-- >>> runTP $ take_cons (Proxy @Integer)
-- Lemma: take_cons @Integer               Q.E.D.
-- [Proven] take_cons @Integer
take_cons :: forall a. SymVal a => Proxy a -> TP Proof
take_cons p =
   lemma (atProxy p "take_cons")
         (\(Forall @"n" n) (Forall @"x" x) (Forall @"xs" (xs :: SList a)) -> n .> 0 .=> take n (x .: xs) .== x .: take (n - 1) xs)
         []

-- | @take n (map f xs) == map f (take n xs)@
--
-- >>> runTPWith (tpRibbon 50 z3) $ take_map @Integer @Float (uninterpret "f")
-- Lemma: take_cons @Integer                         Q.E.D.
-- Lemma: map1 @(Integer,Float)                      Q.E.D.
-- Lemma: take_map.n <= 0 @(Integer,Float)           Q.E.D.
-- Inductive lemma: take_map.n > 0 @(Integer,Float)
--   Step: Base                                      Q.E.D.
--   Step: 1                                         Q.E.D.
--   Step: 2                                         Q.E.D.
--   Step: 3                                         Q.E.D.
--   Step: 4                                         Q.E.D.
--   Step: 5                                         Q.E.D.
--   Result:                                         Q.E.D.
-- Lemma: take_map @(Integer,Float)                  Q.E.D.
-- [Proven] take_map @(Integer,Float)
take_map :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP Proof
take_map f = do
    tc   <- take_cons (Proxy @a)

    map1 <- lemma (atProxy (Proxy @(a, b)) "map1")
                  (\(Forall @"x" x) (Forall @"xs" xs) -> map f (x .: xs) .== f x .: map f xs)
                  []

    h1 <- lemma (atProxy (Proxy @(a, b)) "take_map.n <= 0")
                 (\(Forall @"xs" xs) (Forall @"n" n) -> n .<= 0 .=> take n (map f xs) .== map f (take n xs))
                 []

    h2 <- induct (atProxy (Proxy @(a, b)) "take_map.n > 0")
                 (\(Forall @"xs" xs) (Forall @"n" n) -> n .> 0 .=> take n (map f xs) .== map f (take n xs)) $
                 \ih x xs n -> [n .> 0] |- take n (map f (x .: xs))
                                        =: take n (f x .: map f xs)
                                        =: f x .: take (n - 1) (map f xs) ?? ih   `at` Inst @"n" (n-1)
                                        =: f x .: map f (take (n - 1) xs) ?? map1 `at` (Inst @"x" x, Inst @"xs" (take (n - 1) xs))
                                        =: map f (x .: take (n - 1) xs)   ?? tc
                                        =: map f (take n (x .: xs))
                                        =: qed

    lemma (atProxy (Proxy @(a, b)) "take_map")
          (\(Forall @"xs" xs) (Forall @"n" n) -> take n (map f xs) .== map f (take n xs))
          [h1, h2]

-- | @n .> 0 ==> drop n (x .: xs) == drop (n - 1) xs@
--
-- >>> runTP $ drop_cons (Proxy @Integer)
-- Lemma: drop_cons @Integer               Q.E.D.
-- [Proven] drop_cons @Integer
drop_cons :: forall a. SymVal a => Proxy a -> TP Proof
drop_cons p =
   lemma (atProxy p "drop_cons")
         (\(Forall @"n" n) (Forall @"x" x) (Forall @"xs" (xs :: SList a)) -> n .> 0 .=> drop n (x .: xs) .== drop (n - 1) xs)
         []

-- | @drop n (map f xs) == map f (drop n xs)@
--
-- >>> runTPWith (tpRibbon 50 z3) $ drop_map @Integer @String (uninterpret "f")
-- Lemma: drop_cons @Integer                         Q.E.D.
-- Lemma: drop_cons @[Char]                          Q.E.D.
-- Lemma: drop_map.n <= 0 @(Integer,[Char])          Q.E.D.
-- Inductive lemma: drop_map.n > 0 @(Integer,[Char])
--   Step: Base                                      Q.E.D.
--   Step: 1                                         Q.E.D.
--   Step: 2                                         Q.E.D.
--   Step: 3                                         Q.E.D.
--   Step: 4                                         Q.E.D.
--   Result:                                         Q.E.D.
-- Lemma: drop_map @(Integer,[Char])
--   Step: 1                                         Q.E.D.
--   Step: 2                                         Q.E.D.
--   Step: 3                                         Q.E.D.
--   Step: 4                                         Q.E.D.
--   Result:                                         Q.E.D.
-- [Proven] drop_map @(Integer,[Char])
drop_map :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP Proof
drop_map f = do
   dcA <- drop_cons (Proxy @a)
   dcB <- drop_cons (Proxy @b)

   h1 <- lemma (atProxy (Proxy @(a, b)) "drop_map.n <= 0")
               (\(Forall @"xs" xs) (Forall @"n" n) -> n .<= 0 .=> drop n (map f xs) .== map f (drop n xs))
               []

   h2 <- induct (atProxy (Proxy @(a, b)) "drop_map.n > 0")
                (\(Forall @"xs" xs) (Forall @"n" n) -> n .> 0 .=> drop n (map f xs) .== map f (drop n xs)) $
                \ih x xs n -> [n .> 0] |- drop n (map f (x .: xs))
                                       =: drop n (f x .: map f xs)
                                       ?? dcB `at` (Inst @"n" n, Inst @"x" (f x), Inst @"xs" (map f xs))
                                       =: drop (n - 1) (map f xs)
                                       ?? ih `at` Inst @"n" (n-1)
                                       =: map f (drop (n - 1) xs)
                                       ?? dcA `at` (Inst @"n" n, Inst @"x" x, Inst @"xs" xs)
                                       =: map f (drop n (x .: xs))
                                       =: qed

   -- I'm a bit surprised that z3 can't deduce the following with a simple-lemma, which is essentially a simple case-split.
   -- But the good thing about calc is that it lets us direct the tool in precise ways that we'd like.
   calc (atProxy (Proxy @(a, b)) "drop_map")
        (\(Forall @"xs" xs) (Forall @"n" n) -> drop n (map f xs) .== map f (drop n xs)) $
        \xs n -> [] |- let result = drop n (map f xs) .== map f (drop n xs)
                    in result
                    =: ite (n .<= 0) (n .<= 0 .=> result) (n .> 0 .=> result) ?? h1
                    =: ite (n .<= 0) sTrue                (n .> 0 .=> result) ?? h2
                    =: ite (n .<= 0) sTrue                sTrue
                    =: sTrue
                    =: qed

-- | @n >= 0 ==> length (take n xs) == length xs \`min\` n@
--
-- >>> runTP $ length_take (Proxy @Integer)
-- Lemma: length_take @Integer             Q.E.D.
-- [Proven] length_take @Integer
length_take :: forall a. SymVal a => Proxy a -> TP Proof
length_take p =
     lemma (atProxy p "length_take")
           (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> n .>= 0 .=> length (take n xs) .== length xs `smin` n)
           []

-- | @n >= 0 ==> length (drop n xs) == (length xs - n) \`max\` 0@
--
-- >>> runTP $ length_drop (Proxy @Integer)
-- Lemma: length_drop @Integer             Q.E.D.
-- [Proven] length_drop @Integer
length_drop :: forall a. SymVal a => Proxy a -> TP Proof
length_drop p =
     lemma (atProxy p "length_drop")
           (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> n .>= 0 .=> length (drop n xs) .== (length xs - n) `smax` 0)
           []

-- | @length xs \<= n ==\> take n xs == xs@
--
-- >>> runTP $ take_all (Proxy @Integer)
-- Lemma: take_all @Integer                Q.E.D.
-- [Proven] take_all @Integer
take_all :: forall a. SymVal a => Proxy a -> TP Proof
take_all p =
    lemma (atProxy p "take_all")
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> length xs .<= n .=> take n xs .== xs)
          []

-- | @length xs \<= n ==\> drop n xs == nil@
--
-- >>> runTP $ drop_all (Proxy @Integer)
-- Lemma: drop_all @Integer                Q.E.D.
-- [Proven] drop_all @Integer
drop_all :: forall a. SymVal a => Proxy a -> TP Proof
drop_all p =
    lemma (atProxy p "drop_all")
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> length xs .<= n .=> drop n xs .== nil)
          []

-- | @take n (xs ++ ys) == (take n xs ++ take (n - length xs) ys)@
--
-- >>> runTP $ take_append (Proxy @Integer)
-- Lemma: take_append @Integer             Q.E.D.
-- [Proven] take_append @Integer
take_append :: forall a. SymVal a => Proxy a -> TP Proof
take_append p = lemmaWith cvc5 (atProxy p "take_append")
                  (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) (Forall @"ys" ys)
                      -> take n (xs ++ ys) .== take n xs ++ take (n - length xs) ys)
                  []

-- | @drop n (xs ++ ys) == drop n xs ++ drop (n - length xs) ys@
--
-- NB. As of Feb 2025, z3 struggles to prove this, but cvc5 gets it out-of-the-box.
--
-- >>> runTP $ drop_append (Proxy @Integer)
-- Lemma: drop_append @Integer             Q.E.D.
-- [Proven] drop_append @Integer
drop_append :: forall a. SymVal a => Proxy a -> TP Proof
drop_append p =
    lemmaWith cvc5 (atProxy p "drop_append")
      (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) (Forall @"ys" ys)
            -> drop n (xs ++ ys) .== drop n xs ++ drop (n - length xs) ys)
      []

-- | @length xs == length ys ==> map fst (zip xs ys) = xs@
--
-- >>> runTP $ map_fst_zip (Proxy @(Integer,Integer))
-- Inductive lemma: map_fst_zip @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_fst_zip @(Integer,Integer)
map_fst_zip :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> TP Proof
map_fst_zip p =
   induct (atProxy p "map_fst_zip")
          (\(Forall @"xs" (xs :: SList a), Forall @"ys" (ys :: SList b)) -> length xs .== length ys .=> map fst (zip xs ys) .== xs) $
          \ih (x :: SBV a, xs, y :: SBV b, ys) ->
                [length (x .: xs) .== length (y .: ys)]
             |- map fst (zip (x .: xs) (y .: ys))
             =: map fst (tuple (x, y) .: zip xs ys)
             =: fst (tuple (x, y)) .: map fst (zip xs ys)
             =: x .: map fst (zip xs ys)
             ?? ih
             =: x .: xs
             =: qed

-- | @length xs == length ys ==> map snd (zip xs ys) = xs@
--
-- >>> runTP $ map_snd_zip (Proxy @(Integer,Integer))
-- Inductive lemma: map_snd_zip @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_snd_zip @(Integer,Integer)
map_snd_zip :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> TP Proof
map_snd_zip p =
   induct (atProxy p "map_snd_zip")
          (\(Forall @"xs" (xs :: SList a), Forall @"ys" (ys :: SList b)) -> length xs .== length ys .=> map snd (zip xs ys) .== ys) $
          \ih (x :: SBV a, xs, y :: SBV b, ys) ->
                [length (x .: xs) .== length (y .: ys)]
             |- map snd (zip (x .: xs) (y .: ys))
             =: map snd (tuple (x, y) .: zip xs ys)
             =: snd (tuple (x, y)) .: map snd (zip xs ys)
             =: y .: map snd (zip xs ys)
             ?? ih
             =: y .: ys
             =: qed

-- | @map fst (zip xs ys) == take (min (length xs) (length ys)) xs@
--
-- >>> runTPWith (tpRibbon 55 z3) $ map_fst_zip_take (Proxy @(Integer,Integer))
-- Lemma: take_cons @Integer                              Q.E.D.
-- Inductive lemma: map_fst_zip_take @(Integer,Integer)
--   Step: Base                                           Q.E.D.
--   Step: 1                                              Q.E.D.
--   Step: 2                                              Q.E.D.
--   Step: 3                                              Q.E.D.
--   Step: 4                                              Q.E.D.
--   Step: 5                                              Q.E.D.
--   Result:                                              Q.E.D.
-- [Proven] map_fst_zip_take @(Integer,Integer)
map_fst_zip_take :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> TP Proof
map_fst_zip_take p = do
   tc <- take_cons (Proxy @a)

   induct (atProxy p "map_fst_zip_take")
          (\(Forall @"xs" (xs :: SList a), Forall @"ys" (ys :: SList b)) -> map fst (zip xs ys) .== take (length xs `smin` length ys) xs) $
          \ih (x :: SBV a, xs, y :: SBV b, ys) ->
            [] |- map fst (zip (x .: xs) (y .: ys))
               =: map fst (tuple (x, y) .: zip xs ys)
               =: x .: map fst (zip xs ys)
               ?? ih
               =: x .: take (length xs `smin` length ys) xs
               ?? tc
               =: take (1 + (length xs `smin` length ys)) (x .: xs)
               =: take (length (x .: xs) `smin` length (y .: ys)) (x .: xs)
               =: qed

-- | @map snd (zip xs ys) == take (min (length xs) (length ys)) xs@
--
-- >>> runTP $ map_snd_zip_take (Proxy @(Integer,Integer))
-- Lemma: take_cons @Integer               Q.E.D.
-- Inductive lemma: map_snd_zip_take @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_snd_zip_take @(Integer,Integer)
map_snd_zip_take :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> TP Proof
map_snd_zip_take p = do
   tc <- take_cons (Proxy @a)

   induct (atProxy p "map_snd_zip_take")
          (\(Forall @"xs" (xs :: SList a), Forall @"ys" (ys :: SList b)) -> map snd (zip xs ys) .== take (length xs `smin` length ys) ys) $
          \ih (x :: SBV a, xs, y :: SBV b, ys) ->
               [] |- map snd (zip (x .: xs) (y .: ys))
                  =: map snd (tuple (x, y) .: zip xs ys)
                  =: y .: map snd (zip xs ys)
                  ?? ih
                  =: y .: take (length xs `smin` length ys) ys
                  ?? tc
                  =: take (1 + (length xs `smin` length ys)) (y .: ys)
                  =: take (length (x .: xs) `smin` length (y .: ys)) (y .: ys)
                  =: qed

-- | Count the number of occurrences of an element in a list
count :: SymVal a => SBV a -> SList a -> SInteger
count = smtFunction "count" $ \e l -> ite (null l)
                                          0
                                          (let (x, xs) = uncons l
                                               cxs     = count e xs
                                           in ite (e .== x) (1 + cxs) cxs)

-- | Are the two lists disjoint?
disjoint :: (Eq a, SymVal a) => SList a -> SList a -> SBool
disjoint = smtFunction "disjoint" $ \xs ys -> null xs .|| head xs `notElem` ys .&& disjoint (tail xs) ys

-- | Interleave the elements of two lists. If one ends, we take the rest from the other.
interleave :: SymVal a => SList a -> SList a -> SList a
interleave = smtFunction "interleave" (\xs ys -> ite (null  xs) ys (head xs .: interleave ys (tail xs)))

-- | Prove that interleave preserves total length.
--
-- The induction here is on the total length of the lists, and hence
-- we use the generalized induction principle. We have:
--
-- >>> runTP $ interleaveLen (Proxy @Integer)
-- Inductive lemma (strong): interleaveLen @Integer
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] interleaveLen @Integer
interleaveLen :: forall a. SymVal a => Proxy a -> TP Proof
interleaveLen p = do

   sInduct (atProxy p "interleaveLen")
           (\(Forall @"xs" xs) (Forall @"ys" ys) -> length xs + length ys .== length (interleave @a xs ys))
           (\xs ys -> length @a xs + length @a ys) $
           \ih xs ys ->
              [] |- length xs + length ys .== length (interleave @a xs ys)
                 =: split xs
                          trivial
                          (\a as -> length (a .: as) + length ys .== length (interleave (a .: as) ys)
                                 =: 1 + length as + length ys .== 1 + length (interleave ys as)
                                 ?? ih `at` (Inst @"xs" ys, Inst @"ys" as)
                                 =: sTrue
                                 =: qed)

-- | Uninterleave the elements of two lists. We roughly split it into two, of alternating elements.
uninterleave :: SymVal a => SList a -> STuple [a] [a]
uninterleave lst = uninterleaveGen lst (tuple (nil, nil))

-- | Generalized form of uninterleave with the auxilary lists made explicit.
uninterleaveGen :: SymVal a => SList a -> STuple [a] [a] -> STuple [a] [a]
uninterleaveGen = smtFunction "uninterleave" (\xs alts -> let (es, os) = untuple alts
                                                          in ite (null xs)
                                                                 (tuple (reverse es, reverse os))
                                                                 (uninterleaveGen (tail xs) (tuple (os, head xs .: es))))

-- | The functions 'uninterleave' and 'interleave' are inverses so long as the inputs are of the same length. (The equality
-- would even hold if the first argument has one extra element, but we keep things simple here.)
--
-- We have:
--
-- >>> runTP $ interleaveRoundTrip (Proxy @Integer)
-- Lemma: revCons @Integer                 Q.E.D.
-- Inductive lemma (strong): roundTripGen @Integer
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (4 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.4.1                         Q.E.D.
--     Step: 1.4.2                         Q.E.D.
--     Step: 1.4.3                         Q.E.D.
--     Step: 1.4.4                         Q.E.D.
--     Step: 1.4.5                         Q.E.D.
--     Step: 1.4.6                         Q.E.D.
--     Step: 1.4.7                         Q.E.D.
--     Step: 1.4.8                         Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: interleaveRoundTrip @Integer
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] interleaveRoundTrip @Integer
interleaveRoundTrip :: forall a. SymVal a => Proxy a -> TP Proof
interleaveRoundTrip p = do

   revHelper <- lemma (atProxy p "revCons") (\(Forall @"a" a) (Forall @"as" as) (Forall @"bs" bs)
                      -> reverse @a (a .: as) ++ bs .== reverse as ++ (a .: bs)) []

   -- Generalize the theorem first to take the helper lists explicitly
   roundTripGen <- sInductWith cvc5
         (atProxy p "roundTripGen")
         (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"alts" alts) ->
               length @a xs .== length ys
                  .=> let (es, os) = untuple alts
                      in uninterleaveGen (interleave xs ys) alts .== tuple (reverse es ++ xs, reverse os ++ ys))
         (\xs ys (_alts :: STuple [a] [a]) -> length @a xs + length @a ys) $
         \ih xs ys alts -> [length @a xs .== length ys]
                        |- let (es, os) = untuple alts
                        in uninterleaveGen (interleave xs ys) alts
                        =: split2 (xs, ys)
                                  trivial
                                  trivial
                                  trivial
                                  (\(a, as) (b, bs) -> uninterleaveGen (interleave (a .: as) (b .: bs)) alts
                                                    =: uninterleaveGen (a .: interleave (b .: bs) as) alts
                                                    =: uninterleaveGen (a .: b .: interleave as bs) alts
                                                    =: uninterleaveGen (interleave as bs) (tuple (a .: es, b .: os))
                                                    ?? ih `at` (Inst @"xs" as, Inst @"ys" bs, Inst @"alts" (tuple (a .: es, b .: os)))
                                                    =: tuple (reverse (a .: es) ++ as, reverse (b .: os) ++ bs)
                                                    ?? revHelper `at` (Inst @"a" a, Inst @"as" es, Inst @"bs" as)
                                                    =: tuple (reverse es ++ (a .: as), reverse (b .: os) ++ bs)
                                                    ?? revHelper `at` (Inst @"a" b, Inst @"as" os, Inst @"bs" bs)
                                                    =: tuple (reverse es ++ (a .: as), reverse os ++ (b .: bs))
                                                    =: tuple (reverse es ++ xs, reverse os ++ ys)
                                                    =: qed)

   -- Round-trip theorem:
   calc (atProxy p "interleaveRoundTrip")
           (\(Forall @"xs" xs) (Forall @"ys" ys) -> length xs .== length ys .=> uninterleave (interleave @a xs ys) .== tuple (xs, ys)) $
           \xs ys -> [length xs .== length ys]
                  |- uninterleave (interleave @a xs ys)
                  =: uninterleaveGen (interleave xs ys) (tuple (nil, nil))
                  ?? roundTripGen `at` (Inst @"xs" xs, Inst @"ys" ys, Inst @"alts" (tuple (nil :: SList a, nil :: SList a)))
                  =: tuple (reverse nil ++ xs, reverse nil ++ ys)
                  =: qed
-- | @count e (xs ++ ys) == count e xs + count e ys@
--
-- >>> runTP $ countAppend (Proxy @Integer)
-- Inductive lemma: countAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold count)                Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (simplify)                    Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countAppend @Integer
countAppend :: forall a. SymVal a => Proxy a -> TP Proof
countAppend p =
   induct (atProxy p "countAppend")
          (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"e" (e :: SBV a)) -> count e (xs ++ ys) .== count e xs + count e ys) $
          \ih x xs ys (e :: SBV a) ->
              [] |- count e ((x .: xs) ++ ys)
                 =: count e (x .: (xs ++ ys))
                 ?? "unfold count"
                 =: (let r = count e (xs ++ ys) in ite (e .== x) (1+r) r)
                 ?? ih `at` (Inst @"ys" ys, Inst @"e" e)
                 =: (let r = count e xs + count e ys in ite (e .== x) (1+r) r)
                 ?? "simplify"
                 =: count e (x .: xs) + count e ys
                 =: qed

-- | @count e (take n xs) + count e (drop n xs) == count e xs@
--
-- >>> runTP $ takeDropCount (Proxy @Integer)
-- Inductive lemma: countAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold count)                Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (simplify)                    Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: take_drop @Integer               Q.E.D.
-- Lemma: takeDropCount @Integer
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] takeDropCount @Integer
takeDropCount :: forall a. SymVal a => Proxy a -> TP Proof
takeDropCount p = do
       capp     <- countAppend p
       takeDrop <- take_drop p

       calc (atProxy p "takeDropCount")
            (\(Forall @"xs" xs) (Forall @"n" n) (Forall @"e" (e :: SBV a)) -> count e (take n xs) + count e (drop n xs) .== count e xs) $
            \xs n (e :: SBV a) ->
                [] |- count e (take n xs) + count e (drop n xs)
                   ?? capp `at` (Inst @"xs" (take n xs), Inst @"ys" (drop n xs), Inst @"e" e)
                   =: count e (take n xs ++ drop n xs)
                   ?? takeDrop
                   =: count e xs
                   =: qed

-- | @count xs >= 0@
--
-- >>> runTP $ countNonNeg (Proxy @Integer)
-- Inductive lemma: countNonNeg @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countNonNeg @Integer
countNonNeg :: forall a. SymVal a => Proxy a -> TP Proof
countNonNeg p =
   induct (atProxy p "countNonNeg")
          (\(Forall @"xs" xs) (Forall @"e" (e :: SBV a)) -> count e xs .>= 0) $
          \ih x xs (e :: SBV a) -> [] |- count e (x .: xs) .>= 0
                                      =: cases [ e .== x ==> 1 + count e xs .>= 0
                                                          ?? ih
                                                          =: sTrue
                                                          =: qed
                                               , e ./= x ==> count e xs .>= 0
                                                          ?? ih
                                                          =: sTrue
                                                          =: qed
                                               ]

-- | @e \`elem\` xs ==> count e xs .> 0@
--
-- >>> runTP $ countElem (Proxy @Integer)
-- Inductive lemma: countNonNeg @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: countElem @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countElem @Integer
countElem :: forall a. (Eq a, SymVal a) => Proxy a -> TP Proof
countElem p = do

    cnn <- countNonNeg p

    induct (atProxy p "countElem")
           (\(Forall @"xs" xs) (Forall @"e" (e :: SBV a)) -> e `elem` xs .=> count e xs .> 0) $
           \ih x xs (e :: SBV a) -> [e `elem` (x .: xs)]
                                 |- count e (x .: xs) .> 0
                                 =: cases [ e .== x ==> 1 + count e xs .> 0
                                                     ?? cnn
                                                     =: sTrue
                                                     =: qed
                                          , e ./= x ==> count e xs .> 0
                                                     ?? ih
                                                     =: sTrue
                                                     =: qed
                                          ]

-- | @count e xs .> 0 .=> e \`elem\` xs@
--
-- >>> runTP $ elemCount (Proxy @Integer)
-- Inductive lemma: elemCount @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] elemCount @Integer
elemCount :: forall a. (Eq a, SymVal a) => Proxy a -> TP Proof
elemCount p =
    induct (atProxy p "elemCount")
           (\(Forall @"xs" xs) (Forall @"e" (e :: SBV a)) -> count e xs .> 0 .=> e `elem` xs) $
           \ih x xs (e :: SBV a) -> [count e xs .> 0]
                                 |- e `elem` (x .: xs)
                                 =: cases [ e .== x ==> trivial
                                          , e ./= x ==> e `elem` xs
                                                     ?? ih
                                                     =: sTrue
                                                     =: qed
                                          ]

{- HLint ignore revRev         "Redundant reverse" -}
{- HLint ignore allAny         "Use and"           -}
{- HLint ignore bookKeeping    "Fuse foldr/map"    -}
{- HLint ignore foldrMapFusion "Fuse foldr/map"    -}
{- HLint ignore filterConcat   "Move filter"       -}
{- HLint ignore module         "Use camelCase"     -}
{- HLint ignore module         "Use first"         -}
{- HLint ignore module         "Use second"        -}
{- HLint ignore module         "Use zipWith"       -}
{- HLint ignore mapCompose     "Use map once"      -}
