-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.TP.List
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
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP.List (
     -- * Append
     appendNull, consApp, appendAssoc, initsLength, tailsLength, tailsAppend

     -- * Reverse
   , revLen, revApp, revCons, revSnoc, revRev, enumLen, revNM

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
   , filterAppend, filterConcat, takeDropWhile

     -- * Stutter removal
   , destutter, destutterIdempotent

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

import Prelude (Integer, Bool, Eq, ($), Num(..), id, (.), flip)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
-- >>> import Control.Exception
#endif

-- | @xs ++ [] == xs@
--
-- >>> runTP $ appendNull @Integer
-- Lemma: appendNull                       Q.E.D.
-- [Proven] appendNull :: Ɐxs ∷ [Integer] → Bool
appendNull :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
appendNull = lemma "appendNull"
                   (\(Forall xs) -> xs ++ nil .== xs)
                   []

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- >>> runTP $ consApp @Integer
-- Lemma: consApp                          Q.E.D.
-- [Proven] consApp :: Ɐx ∷ Integer → Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
consApp :: forall a. SymVal a => TP (Proof (Forall "x" a -> Forall "xs" [a] -> Forall "ys" [a] -> SBool))
consApp = lemma "consApp"
                (\(Forall x) (Forall xs) (Forall ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys))
                []

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- >>> runTP $ appendAssoc @Integer
-- Lemma: appendAssoc                      Q.E.D.
-- [Proven] appendAssoc :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Ɐzs ∷ [Integer] → Bool
--
-- Surprisingly, z3 can prove this without any induction. (Since SBV's append translates directly to
-- the concatenation of sequences in SMTLib, it must trigger an internal heuristic in z3
-- that proves it right out-of-the-box!)
appendAssoc :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> Forall "zs" [a] -> SBool))
appendAssoc =
   lemma "appendAssoc"
         (\(Forall xs) (Forall ys) (Forall zs) -> xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs)
         []

-- | @length (inits xs) == 1 + length xs@
--
-- >>> runTP $ initsLength @Integer
-- Inductive lemma (strong): initsLength
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] initsLength :: Ɐxs ∷ [Integer] → Bool
initsLength :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
initsLength =
   sInduct "initsLength"
           (\(Forall xs) -> length (inits xs) .== 1 + length xs)
           (length @a) $
           \ih xs -> [] |- length (inits xs)
                        ?? ih
                        =: 1 + length xs
                        =: qed

-- | @length (tails xs) == 1 + length xs@
--
-- >>> runTP $ tailsLength @Integer
-- Inductive lemma: tailsLength
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] tailsLength :: Ɐxs ∷ [Integer] → Bool
tailsLength :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
tailsLength =
   induct "tailsLength"
          (\(Forall xs) -> length (tails xs) .== 1 + length xs) $
          \ih (x, xs) -> [] |- length (tails (x .: xs))
                            =: length (tails xs ++ [x .: xs])
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
-- >>> runTP $ tailsAppend @Integer
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
-- Inductive lemma: tailsAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] tailsAppend :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
tailsAppend :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
tailsAppend = do

   let -- Ideally, we would like to define appendEach like this:
       --
       --       appendEach xs ys = map (++ ys) xs
       --
       -- But capture of ys is not allowed when we use the higher-order
       -- function map in SBV. So, we create a closure instead.
       appendEach :: SList a -> SList [a] -> SList [a]
       appendEach ys = map $ Closure { closureEnv = ys
                                     , closureFun = \env xs -> xs ++ env
                                     }

   -- Even proving the base case of induction is hard due to recursive definition. So we first prove the base case by induction.
   bc <- induct "base case"
                (\(Forall @"ys" (ys :: SList a)) -> tails ys .== [ys] ++ tail (tails ys)) $
                \ih (y, ys) -> [] |- tails (y .: ys)
                                  =: [y .: ys] ++ tails ys
                                  ?? ih
                                  =: [y .: ys] ++ [ys] ++ tail (tails ys)
                                  =: [y .: ys] ++ tail (tails (y .: ys))
                                  =: qed

   -- Also need a helper to relate how appendEach and tails work together
   helper <- calc "helper"
                   (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"x" x) ->
                        appendEach ys (tails (x .: xs)) .== [(x .: xs) ++ ys] ++ appendEach ys (tails xs)) $
                   \xs ys x -> [] |- appendEach ys (tails (x .: xs))
                                  =: appendEach ys ([x .: xs] ++ tails xs)
                                  =: [(x .: xs) ++ ys] ++ appendEach ys (tails xs)
                                  =: qed

   induct "tailsAppend"
          (\(Forall xs) (Forall ys) -> tails (xs ++ ys) .== appendEach ys (tails xs) ++ tail (tails ys)) $
          \ih (x, xs) ys -> [assumptionFromProof bc]
                         |- tails ((x .: xs) ++ ys)
                         =: tails (x .: (xs ++ ys))
                         =: [x .: (xs ++ ys)] ++ tails (xs ++ ys)
                         ?? ih
                         =: [(x .: xs) ++ ys] ++ appendEach ys (tails xs) ++ tail (tails ys)
                         ?? helper
                         =: appendEach ys (tails (x .: xs)) ++ tail (tails ys)
                         =: qed

-- | @length xs == length (reverse xs)@
--
-- >>> runTP $ revLen @Integer
-- Inductive lemma: revLen
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revLen :: Ɐxs ∷ [Integer] → Bool
revLen :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
revLen = induct "revLen"
                (\(Forall xs) -> length (reverse xs) .== length xs) $
                \ih (x, xs) -> [] |- length (reverse (x .: xs))
                                  =: length (reverse xs ++ [x])
                                  =: length (reverse xs) + length [x]
                                  ?? ih
                                  =: length xs + 1
                                  =: length (x .: xs)
                                  =: qed

-- | @reverse (xs ++ ys) .== reverse ys ++ reverse xs@
--
-- >>> runTP $ revApp @Integer
-- Inductive lemma: revApp
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revApp :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
revApp :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
revApp = induct "revApp"
                 (\(Forall xs) (Forall ys) -> reverse (xs ++ ys) .== reverse ys ++ reverse xs) $
                 \ih (x, xs) ys -> [] |- reverse ((x .: xs) ++ ys)
                                      =: reverse (x .: (xs ++ ys))
                                      =: reverse (xs ++ ys) ++ [x]
                                      ?? ih
                                      =: (reverse ys ++ reverse xs) ++ [x]
                                      =: reverse ys ++ (reverse xs ++ [x])
                                      =: reverse ys ++ reverse (x .: xs)
                                      =: qed

-- | @reverse (x:xs) == reverse xs ++ [x]@
--
-- >>> runTP $ revCons @Integer
-- Lemma: revCons                          Q.E.D.
-- [Proven] revCons :: Ɐx ∷ Integer → Ɐxs ∷ [Integer] → Bool
revCons :: forall a. SymVal a => TP (Proof (Forall "x" a -> Forall "xs" [a] -> SBool))
revCons = lemma "revCons"
                (\(Forall x) (Forall xs) -> reverse (x .: xs) .== reverse xs ++ [x])
                []

-- | @reverse (xs ++ [x]) == x : reverse xs@
--
-- >>> runTP $ revSnoc @Integer
-- Inductive lemma: revApp
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: revSnoc                          Q.E.D.
-- [Proven] revSnoc :: Ɐx ∷ Integer → Ɐxs ∷ [Integer] → Bool
revSnoc :: forall a. SymVal a => TP (Proof (Forall "x" a -> Forall "xs" [a] -> SBool))
revSnoc = do
   ra <- revApp @a

   lemma "revSnoc"
         (\(Forall x) (Forall xs) -> reverse (xs ++ [x]) .== x .: reverse xs)
         [proofOf ra]

-- | @reverse (reverse xs) == xs@
--
-- >>> runTP $ revRev @Integer
-- Inductive lemma: revApp
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revRev
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revRev :: Ɐxs ∷ [Integer] → Bool
revRev :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
revRev = do

   ra <- revApp @a

   induct "revRev"
          (\(Forall xs) -> reverse (reverse xs) .== xs) $
          \ih (x, xs) -> [] |- reverse (reverse (x .: xs))
                            =: reverse (reverse xs ++ [x])
                            ?? ra
                            =: reverse [x] ++ reverse (reverse xs)
                            ?? ih
                            =: [x] ++ xs
                            =: x .: xs
                            =: qed

-- | \(\text{length } [n \dots m] = \max(0,\; m - n + 1)\)
--
-- The proof uses the metric @|m-n|@.
--
-- >>> runTP enumLen
-- Inductive lemma (strong): enumLen
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] enumLen :: Ɐn ∷ Integer → Ɐm ∷ Integer → Bool
enumLen :: TP (Proof (Forall "n" Integer -> Forall "m" Integer -> SBool))
enumLen =
  sInduct "enumLen"
          (\(Forall n) (Forall m) -> length [sEnum|n .. m|] .== 0 `smax` (m - n + 1))
          (\n m -> abs (m - n)) $
          \ih n m -> [] |- length [sEnum|n+1 .. m|]
                        =: cases [ n+1 .>  m ==> trivial
                                 , n+1 .<= m ==> length (n+1 .: [sEnum|n+2 .. m|])
                                              =: 1 + length [sEnum|n+2 .. m|]
                                              ?? ih
                                              =: 1 + (0 `smax` (m - (n+2) + 1))
                                              =: 0 `smax` (m - (n+1) + 1)
                                              =: qed
                                 ]

-- | @reverse [n .. m] == [m, m-1 .. n]@
--
-- The proof uses the metric @|m-n|@.
--
-- >>> runTP $ revNM
-- Inductive lemma (strong): helper
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): revNM
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revNM :: Ɐn ∷ Integer → Ɐm ∷ Integer → Bool
revNM :: TP (Proof (Forall "n" Integer -> Forall "m" Integer -> SBool))
revNM = do

  helper <- sInduct "helper"
                    (\(Forall @"m" (m :: SInteger)) (Forall @"n" n) ->
                          n .< m .=> [sEnum|m, m-1 .. n+1|] ++ [n] .== [sEnum|m, m-1 .. n|])
                    (\m n -> abs (m - n)) $
                    \ih m n -> [n .< m] |- [sEnum|m, m-1 .. n+1|] ++ [n]
                                        =: m .: [sEnum|m-1, m-2 .. n+1|] ++ [n]
                                        ?? ih
                                        =: m .: [sEnum|m-1, m-2 .. n|]
                                        =: [sEnum|m, m-1 .. n|]
                                        =: qed

  sInduct "revNM"
          (\(Forall n) (Forall m) -> reverse [sEnum|n .. m|] .== [sEnum|m, m-1 .. n|])
          (\n m -> abs (m - n)) $
          \ih n m -> [] |- reverse [sEnum|n .. m|]
                        =: cases [ n .>  m ==> trivial
                                 , n .<= m ==> reverse (n .: [sEnum|(n+1) .. m|])
                                            =: reverse [sEnum|(n+1) .. m|] ++ [n]
                                            ?? ih
                                            =: [sEnum|m, m-1 .. n+1|] ++ [n]
                                            ?? helper
                                            =: [sEnum|m, m-1 .. n|]
                                            =: qed
                                 ]

-- | @length (x : xs) == 1 + length xs@
--
-- >>> runTP $ lengthTail @Integer
-- Lemma: lengthTail                       Q.E.D.
-- [Proven] lengthTail :: Ɐx ∷ Integer → Ɐxs ∷ [Integer] → Bool
lengthTail :: forall a. SymVal a => TP (Proof (Forall "x" a -> Forall "xs" [a] -> SBool))
lengthTail = lemma "lengthTail"
                   (\(Forall x) (Forall xs) -> length (x .: xs) .== 1 + length xs)
                   []

-- | @length (xs ++ ys) == length xs + length ys@
--
-- >>> runTP $ lenAppend @Integer
-- Lemma: lenAppend                        Q.E.D.
-- [Proven] lenAppend :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
lenAppend :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
lenAppend = lemma "lenAppend"
                  (\(Forall xs) (Forall ys) -> length (xs ++ ys) .== length xs + length ys)
                  []

-- | @length xs == length ys -> length (xs ++ ys) == 2 * length xs@
--
-- >>> runTP $ lenAppend2 @Integer
-- Lemma: lenAppend2                       Q.E.D.
-- [Proven] lenAppend2 :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
lenAppend2 :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
lenAppend2 = lemma "lenAppend2"
                   (\(Forall xs) (Forall ys) -> length xs .== length ys .=> length (xs ++ ys) .== 2 * length xs)
                   []

-- | @length (replicate k x) == max (0, k)@
--
-- >>> runTP $ replicateLength @Integer
-- Inductive lemma: replicateLength
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] replicateLength :: Ɐk ∷ Integer → Ɐx ∷ Integer → Bool
replicateLength :: forall a. SymVal a => TP (Proof (Forall "k" Integer -> Forall "x" a -> SBool))
replicateLength = induct "replicateLength"
                         (\(Forall k) (Forall x) -> length (replicate k x) .== 0 `smax` k) $
                         \ih k x -> [] |- length (replicate (k+1) x)
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
-- [Proven] allAny :: Ɐxs ∷ [Bool] → Bool
allAny :: TP (Proof (Forall "xs" [Bool] -> SBool))
allAny = induct "allAny"
                (\(Forall xs) -> sNot (all id xs) .== any sNot xs) $
                \ih (x, xs) -> [] |- sNot (all id (x .: xs))
                                  =: sNot (x .&& all id xs)
                                  =: (sNot x .|| sNot (all id xs))
                                  ?? ih
                                  =: sNot x .|| any sNot xs
                                  =: any sNot (x .: xs)
                                  =: qed

-- | @f == g ==> map f xs == map g xs@
--
-- >>> runTP $ mapEquiv @Integer @Integer (uninterpret "f") (uninterpret "g")
-- Inductive lemma: mapEquiv
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapEquiv :: Ɐxs ∷ [Integer] → Bool
mapEquiv :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> (SBV a -> SBV b) -> TP (Proof (Forall "xs" [a] -> SBool))
mapEquiv f g = do
   let f'eq'g :: SBool
       f'eq'g = quantifiedBool $ \(Forall x) -> f x .== g x

   induct "mapEquiv"
          (\(Forall xs) -> f'eq'g .=> map f xs .== map g xs) $
          \ih (x, xs) -> [f'eq'g] |- map f (x .: xs) .== map g (x .: xs)
                                  =: f x .: map f xs .== g x .: map g xs
                                  =: f x .: map f xs .== f x .: map g xs
                                  ?? ih
                                  =: f x .: map f xs .== f x .: map f xs
                                  =: map f (x .: xs) .== map f (x .: xs)
                                  =: qed

-- | @map f (xs ++ ys) == map f xs ++ map f ys@
--
-- >>> runTP $ mapAppend @Integer @Integer (uninterpret "f")
-- Inductive lemma: mapAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapAppend :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
mapAppend :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
mapAppend f =
   induct "mapAppend"
          (\(Forall xs) (Forall ys) -> map f (xs ++ ys) .== map f xs ++ map f ys) $
          \ih (x, xs) ys -> [] |- map f ((x .: xs) ++ ys)
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
-- Inductive lemma: mapAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: mapReverse
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapReverse :: Ɐxs ∷ [Integer] → Bool
mapReverse :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP (Proof (Forall "xs" [a] -> SBool))
mapReverse f = do
     mApp <- mapAppend f

     induct "mapReverse"
            (\(Forall xs) -> reverse (map f xs) .== map f (reverse xs)) $
            \ih (x, xs) -> [] |- reverse (map f (x .: xs))
                              =: reverse (f x .: map f xs)
                              =: reverse (map f xs) ++ [f x]
                              ?? ih
                              =: map f (reverse xs) ++ [f x]
                              =: map f (reverse xs) ++ map f [x]
                              ?? mApp
                              =: map f (reverse xs ++ [x])
                              =: map f (reverse (x .: xs))
                              =: qed

-- | @map f . map g == map (f . g)@
--
-- >>> runTP $ mapCompose @Integer @Bool @String (uninterpret "f") (uninterpret "g")
-- Inductive lemma: mapCompose
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapCompose :: Ɐxs ∷ [Integer] → Bool
mapCompose :: forall a b c. (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b) -> (SBV b -> SBV c) -> TP (Proof (Forall "xs" [a] -> SBool))
mapCompose f g =
  induct "mapCompose"
         (\(Forall xs) -> map g (map f xs) .== map (g . f) xs) $
         \ih (x, xs) -> [] |- map g (map f (x .: xs))
                           =: map g (f x .: map f xs)
                           =: g (f x) .: map g (map f xs)
                           ?? ih
                           =: g (f x) .: map (g . f) xs
                           =: (g . f) x .: map (g . f) xs
                           =: map (g . f) (x .: xs)
                           =: qed

-- | @foldr f a . map g == foldr (f . g) a@
--
-- >>> runTP $ foldrMapFusion @String @Bool @Integer (uninterpret "a") (uninterpret "b") (uninterpret "c")
-- Inductive lemma: foldrMapFusion
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrMapFusion :: Ɐxs ∷ [[Char]] → Bool
foldrMapFusion :: forall a b c. (SymVal a, SymVal b, SymVal c) => SBV c -> (SBV a -> SBV b) -> (SBV b -> SBV c -> SBV c) -> TP (Proof (Forall "xs" [a] -> SBool))
foldrMapFusion a g f =
  induct "foldrMapFusion"
         (\(Forall xs) -> foldr f a (map g xs) .== foldr (f . g) a xs) $
         \ih (x, xs) -> [] |- foldr f a (map g (x .: xs))
                           =: foldr f a (g x .: map g xs)
                           =: g x `f` foldr f a (map g xs)
                           ?? ih
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
-- >>> runTP $ foldrFusion @String @Bool @Integer (uninterpret "a") (uninterpret "b") (uninterpret "f") (uninterpret "g") (uninterpret "h")
-- Inductive lemma: foldrFusion
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFusion :: Ɐxs ∷ [[Char]] → Bool
foldrFusion :: forall a b c. (SymVal a, SymVal b, SymVal c) => SBV c -> SBV b -> (SBV c -> SBV b) -> (SBV a -> SBV c -> SBV c) -> (SBV a -> SBV b -> SBV b) -> TP (Proof (Forall "xs" [a] -> SBool))
foldrFusion a b f g h = do
   let -- Assumptions under which the equality holds
       h1 = f a .== b
       h2 = quantifiedBool $ \(Forall x) (Forall y) -> f (g x y) .== h x (f y)

   induct "foldrFusion"
          (\(Forall xs) -> h1 .&& h2 .=> f (foldr g a xs) .== foldr h b xs) $
          \ih (x, xs) -> [h1, h2] |- f (foldr g a (x .: xs))
                                  =: f (g x (foldr g a xs))
                                  =: h x (f (foldr g a xs))
                                  ?? ih
                                  =: h x (foldr h b xs)
                                  =: foldr h b (x .: xs)
                                  =: qed

-- | @foldr f a (xs ++ ys) == foldr f (foldr f a ys) xs@
--
-- >>> runTP $ foldrOverAppend @Integer (uninterpret "a") (uninterpret "f")
-- Inductive lemma: foldrOverAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrOverAppend :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
foldrOverAppend :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
foldrOverAppend a f =
   induct "foldrOverAppend"
          (\(Forall xs) (Forall ys) -> foldr f a (xs ++ ys) .== foldr f (foldr f a ys) xs) $
          \ih (x, xs) ys -> [] |- foldr f a ((x .: xs) ++ ys)
                               =: foldr f a (x .: (xs ++ ys))
                               =: x `f` foldr f a (xs ++ ys)
                               ?? ih
                               =: x `f` foldr f (foldr f a ys) xs
                               =: foldr f (foldr f a ys) (x .: xs)
                               =: qed

-- | @foldl f e (xs ++ ys) == foldl f (foldl f e xs) ys@
--
-- >>> runTP $ foldlOverAppend @Integer @Bool (uninterpret "f")
-- Inductive lemma: foldlOverAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldlOverAppend :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Ɐe ∷ Bool → Bool
foldlOverAppend :: forall a b. (SymVal a, SymVal b) => (SBV b -> SBV a -> SBV b) -> TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> Forall "e" b -> SBool))
foldlOverAppend f =
   induct "foldlOverAppend"
          (\(Forall xs) (Forall ys) (Forall a) -> foldl f a (xs ++ ys) .== foldl f (foldl f a xs) ys) $
          \ih (x, xs) ys a -> [] |- foldl f a ((x .: xs) ++ ys)
                                 =: foldl f a (x .: (xs ++ ys))
                                 =: foldl f (a `f` x) (xs ++ ys)
                                 -- z3 is smart enough to instantiate the IH correctly below, but we're
                                 -- using an explicit instantiation to be clear about the use of @a@ at a different value
                                 ?? ih `at` (Inst @"ys" ys, Inst @"e" (a `f` x))
                                 =: foldl f (foldl f (a `f` x) xs) ys
                                 =: qed

-- | @foldr f e xs == foldl (flip f) e (reverse xs)@
--
-- >>> runTP $ foldrFoldlDuality @Integer @String (uninterpret "f")
-- Inductive lemma: foldlOverAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrFoldlDuality
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFoldlDuality :: Ɐxs ∷ [Integer] → Ɐe ∷ [Char] → Bool
foldrFoldlDuality :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> TP (Proof (Forall "xs" [a] -> Forall "e" b -> SBool))
foldrFoldlDuality f = do
   foa <- foldlOverAppend (flip f)

   induct "foldrFoldlDuality"
          (\(Forall xs) (Forall e) -> foldr f e xs .== foldl (flip f) e (reverse xs)) $
          \ih (x, xs) e -> [] |- let ff  = flip f
                                     rxs = reverse xs
                                 in foldr f e (x .: xs)
                                 =: x `f` foldr f e xs
                                 ?? ih
                                 =: x `f` foldl ff e rxs
                                 =: foldl ff e rxs `ff` x
                                 =: foldl ff (foldl ff e rxs) [x]
                                 ?? foa
                                 =: foldl ff e (rxs ++ [x])
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
-- Inductive lemma: helper
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrFoldlDuality
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFoldlDuality :: Ɐxs ∷ [Integer] → Bool
foldrFoldlDualityGeneralized :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> TP (Proof (Forall "xs" [a] -> SBool))
foldrFoldlDualityGeneralized e (@) = do
   -- Assumptions under which the equality holds
   let assoc = quantifiedBool $ \(Forall x) (Forall y) (Forall z) -> x @ (y @ z) .== (x @ y) @ z
       lunit = quantifiedBool $ \(Forall x) -> e @ x .== x
       runit = quantifiedBool $ \(Forall x) -> x @ e .== x

   -- Helper: foldl (@) (y @ z) xs = y @ foldl (@) z xs
   -- Note the instantiation of the IH at a different value for z. It turns out
   -- we don't have to actually specify this since z3 can figure it out by itself, but we're being explicit.
   helper <- induct "helper"
                    (\(Forall @"xs" xs) (Forall @"y" y) (Forall @"z" z) -> assoc .=> foldl (@) (y @ z) xs .== y @ foldl (@) z xs) $
                    \ih (x, xs) y z -> [assoc] |- foldl (@) (y @ z) (x .: xs)
                                               =: foldl (@) ((y @ z) @ x) xs
                                               ?? assoc
                                               =: foldl (@) (y @ (z @ x)) xs
                                               ?? ih `at` (Inst @"y" y, Inst @"z" (z @ x))
                                               =: y @ foldl (@) (z @ x) xs
                                               =: y @ foldl (@) z (x .: xs)
                                               =: qed

   induct "foldrFoldlDuality"
          (\(Forall xs) -> assoc .&& lunit .&& runit .=> foldr (@) e xs .== foldl (@) e xs) $
          \ih (x, xs) -> [assoc, lunit, runit] |- foldr (@) e (x .: xs)
                                               =: x @ foldr (@) e xs
                                               ?? ih
                                               =: x @ foldl (@) e xs
                                               ?? helper
                                               =: foldl (@) (x @ e) xs
                                               ?? runit
                                               =: foldl (@) x xs
                                               ?? lunit
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
-- Inductive lemma: foldl over <*>/<+>
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrFoldl
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFoldl :: Ɐxs ∷ [Integer] → Bool
foldrFoldl :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> (SBV b -> SBV a -> SBV b) -> SBV b-> TP (Proof (Forall "xs" [a] -> SBool))
foldrFoldl (<+>) (<*>) e = do
   -- Assumptions about the operators
   let -- (x <+> y) <*> z == x <+> (y <*> z)
       assoc = quantifiedBool $ \(Forall x) (Forall y) (Forall z) -> (x <+> y) <*> z .== x <+> (y <*> z)

       -- x <+> e == e <*> x
       unit  = quantifiedBool $ \(Forall x) -> x <+> e .== e <*> x

   -- Helper: x <+> foldl (<*>) y xs == foldl (<*>) (x <+> y) xs
   helper <-
      induct "foldl over <*>/<+>"
             (\(Forall @"xs" xs) (Forall @"x" x) (Forall @"y" y) -> assoc .=> x <+> foldl (<*>) y xs .== foldl (<*>) (x <+> y) xs) $

             -- Using z to avoid confusion with the variable x already present, following Bird.
             -- z3 can figure out the proper instantiation of ih so the at call is unnecessary, but being explicit is helpful.
             \ih (z, xs) x y -> [assoc] |- x <+> foldl (<*>) y (z .: xs)
                                        =: x <+> foldl (<*>) (y <*> z) xs
                                        ?? ih `at` (Inst @"x" x, Inst @"y" (y <*> z))
                                        =: foldl (<*>) (x <+> (y <*> z)) xs
                                        ?? assoc
                                        =: foldl (<*>) ((x <+> y) <*> z) xs
                                        =: foldl (<*>) (x <+> y) (z .: xs)
                                        =: qed

   -- Final proof:
   induct "foldrFoldl"
          (\(Forall xs) -> assoc .&& unit .=> foldr (<+>) e xs .== foldl (<*>) e xs) $
          \ih (x, xs) -> [assoc, unit] |- foldr (<+>) e (x .: xs)
                                       =: x <+> foldr (<+>) e xs
                                       ?? ih
                                       =: x <+> foldl (<*>) e xs
                                       ?? helper
                                       =: foldl (<*>) (x <+> e) xs
                                       =: foldl (<*>) (e <*> x) xs
                                       =: foldl (<*>) e (x .: xs)
                                       =: qed

-- | Provided @f@ is associative and @a@ is its both left and right-unit:
--
-- @foldr f a . concat == foldr f a . map (foldr f a)@
--
-- >>> runTP $ bookKeeping @Integer (uninterpret "a") (uninterpret "f")
-- Inductive lemma: foldBase
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: foldrOverAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: bookKeeping
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] bookKeeping :: Ɐxss ∷ [[Integer]] → Bool
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
bookKeeping :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> TP (Proof (Forall "xss" [[a]] -> SBool))
bookKeeping a f = do

   -- Assumptions about f
   let assoc = quantifiedBool $ \(Forall x) (Forall y) (Forall z) -> x `f` (y `f` z) .== (x `f` y) `f` z
       rUnit = quantifiedBool $ \(Forall x) -> x `f` a .== x
       lUnit = quantifiedBool $ \(Forall x) -> a `f` x .== x

   -- Helper: @foldr f y xs = foldr f a xs `f` y@
   helper <- induct "foldBase"
                    (\(Forall xs) (Forall y) -> lUnit .&& assoc .=> foldr f y xs .== foldr f a xs `f` y) $
                    \ih (x, xs) y -> [lUnit, assoc] |- foldr f y (x .: xs)
                                                    =: x `f` foldr f y xs
                                                    ?? ih
                                                    =: x `f` (foldr f a xs `f` y)
                                                    =: (x `f` foldr f a xs) `f` y
                                                    =: foldr f a (x .: xs) `f` y
                                                    =: qed

   foa <- foldrOverAppend a f

   induct "bookKeeping"
          (\(Forall xss) -> assoc .&& rUnit .&& lUnit .=> foldr f a (concat xss) .== foldr f a (map (foldr f a) xss)) $
          \ih (xs, xss) -> [assoc, rUnit, lUnit] |- foldr f a (concat (xs .: xss))
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
-- Inductive lemma: filterAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] filterAppend :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
filterAppend :: forall a. SymVal a => (SBV a -> SBool) -> TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
filterAppend p =
   induct "filterAppend"
          (\(Forall xs) (Forall ys) -> filter p xs ++ filter p ys .== filter p (xs ++ ys)) $
          \ih (x, xs) ys -> [] |- filter p (x .: xs) ++ filter p ys
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
-- Inductive lemma: filterAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: filterConcat
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] filterConcat :: Ɐxss ∷ [[Integer]] → Bool
filterConcat :: forall a. SymVal a => (SBV a -> SBool) -> TP (Proof (Forall "xss" [[a]] -> SBool))
filterConcat p = do
  fa <- filterAppend p

  inductWith cvc5 "filterConcat"
         (\(Forall xss) -> filter p (concat xss) .== concatMap (filter p) xss) $
         \ih (xs, xss) -> [] |- filter p (concat (xs .: xss))
                             =: filter p (xs ++ concat xss)
                             ?? fa
                             =: filter p xs ++ filter p (concat xss)
                             ?? ih
                             =: concatMap (filter p) (xs .: xss)
                             =: qed

-- | @takeWhile f xs ++ dropWhile f xs == xs@
--
-- >>> runTP $ takeDropWhile @Integer (uninterpret "f")
-- Inductive lemma: takeDropWhile
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] takeDropWhile :: Ɐxs ∷ [Integer] → Bool
takeDropWhile :: forall a. SymVal a => (SBV a -> SBool) -> TP (Proof (Forall "xs" [a] -> SBool))
takeDropWhile f =
   induct "takeDropWhile"
          (\(Forall xs) -> takeWhile f xs ++ dropWhile f xs .== xs) $
          \ih (x, xs) -> [] |- takeWhile f (x .: xs) ++ dropWhile f (x .: xs)
                            =: cases [ f x        ==> x .: takeWhile f xs ++ dropWhile f xs
                                                   ?? ih
                                                   =: x .: xs
                                                   =: qed
                                     , sNot (f x) ==> [] ++ x .: xs
                                                   =: x .: xs
                                                   =: qed
                                     ]
-- | Remove adjacent duplicates.
destutter :: SymVal a => SList a -> SList a
destutter = smtFunction "destutter" $ \xs -> ite (null xs .|| null (tail xs))
                                                 xs
                                                 (let (a, as) = uncons xs
                                                      r       = destutter as
                                                  in ite (a .== head as) r (a .: r))

-- | @destutter (destutter xs) == destutter xs@
--
-- >>> runTP $ destutterIdempotent @Integer
-- Inductive lemma: helper1
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: helper2
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): helper3
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2 (2 way full case split)
--       Step: 1.2.1                       Q.E.D.
--       Step: 1.2.2.1                     Q.E.D.
--       Step: 1.2.2.2 (2 way case split)
--         Step: 1.2.2.2.1.1               Q.E.D.
--         Step: 1.2.2.2.1.2               Q.E.D.
--         Step: 1.2.2.2.2.1               Q.E.D.
--         Step: 1.2.2.2.2.2               Q.E.D.
--         Step: 1.2.2.2.Completeness      Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: destutterIdempotent              Q.E.D.
-- [Proven] destutterIdempotent :: Ɐxs ∷ [Integer] → Bool
destutterIdempotent :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
destutterIdempotent = do

   -- No adjacent duplicates
   let noAdd = smtFunction "noAdd" $ \xs -> null xs .|| null (tail xs) .|| (head xs ./= head (tail xs) .&& noAdd (tail xs))

   -- Helper: The head of a destuttered non-empty list does not change
   helper1 <- induct "helper1"
                     (\(Forall @"xs" (xs :: SList a)) (Forall @"h" h) -> head (destutter (h .: xs)) .== h) $
                     \ih (x, xs) h -> []
                                   |- head (destutter (h .: x .: xs))
                                   =: cases [ h ./= x ==> trivial
                                            , h .== x ==> head (destutter (x .: xs))
                                                       ?? ih
                                                       =: x
                                                       =: qed
                                            ]

   -- Helper: show that if a list has no adjacent duplicates, then destutter leaves it unchanged:
   helper2 <- induct "helper2"
                     (\(Forall @"xs" (xs :: SList a)) -> noAdd xs .=> destutter xs .== xs) $
                     \ih (x, xs) -> [noAdd (x .: xs)]
                                 |- destutter (x .: xs)
                                 ?? ih
                                 =: x .: xs
                                 =: qed

   -- Helper: prove that noAdd is true for the result of destutter
   helper3 <- sInductWith cvc5 "helper3"
                  (\(Forall @"xs" (xs :: SList a)) -> noAdd (destutter xs))
                  length $
                  \ih xs -> []
                         |- noAdd (destutter xs)
                         =: split xs
                                  trivial
                                  (\a as -> split as
                                                  trivial
                                                  (\b bs -> noAdd (destutter (a .: b .: bs))
                                                         =: cases [a .== b  ==> noAdd (destutter (b .: bs))
                                                                             ?? ih
                                                                             =: sTrue
                                                                             =: qed
                                                                  , a ./= b ==> noAdd (a .: destutter (b .: bs))
                                                                             ?? helper1 `at` (Inst @"xs" bs, Inst @"h" b)
                                                                             ?? ih
                                                                             =: sTrue
                                                                             =: qed
                                                                  ]))

   -- Now we can prove idempotency easily:
   lemma "destutterIdempotent"
          (\(Forall xs) -> destutter (destutter xs) .== destutter xs)
          [proofOf helper2, proofOf helper3]

-- | @(as ++ bs) \\ cs == (as \\ cs) ++ (bs \\ cs)@
--
-- >>> runTP $ appendDiff @Integer
-- Inductive lemma: appendDiff
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] appendDiff :: Ɐas ∷ [Integer] → Ɐbs ∷ [Integer] → Ɐcs ∷ [Integer] → Bool
appendDiff :: forall a. (Eq a, SymVal a) => TP (Proof (Forall "as" [a] -> Forall "bs" [a] -> Forall "cs" [a] -> SBool))
appendDiff = induct "appendDiff"
                    (\(Forall as) (Forall bs) (Forall cs) -> (as ++ bs) \\ cs .== (as \\ cs) ++ (bs \\ cs)) $
                    \ih (a, as) bs cs -> [] |- (a .: as ++ bs) \\ cs
                                            =: (a .: (as ++ bs)) \\ cs
                                            =: ite (a `elem` cs) ((as ++ bs) \\ cs) (a .: ((as ++ bs) \\ cs))
                                            ?? ih
                                            =: ((a .: as) \\ cs) ++ (bs \\ cs)
                                            =: qed

-- | @as \\ (bs ++ cs) == (as \\ bs) \\ cs@
--
-- >>> runTP $ diffAppend @Integer
-- Inductive lemma: diffAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] diffAppend :: Ɐas ∷ [Integer] → Ɐbs ∷ [Integer] → Ɐcs ∷ [Integer] → Bool
diffAppend :: forall a. (Eq a, SymVal a) => TP (Proof (Forall "as" [a] -> Forall "bs" [a] -> Forall "cs" [a] -> SBool))
diffAppend = induct "diffAppend"
                    (\(Forall as) (Forall bs) (Forall cs) -> as \\ (bs ++ cs) .== (as \\ bs) \\ cs) $
                    \ih (a, as) bs cs -> [] |- (a .: as) \\ (bs ++ cs)
                                            =: ite (a `elem` (bs ++ cs)) (as \\ (bs ++ cs)) (a .: (as \\ (bs ++ cs)))
                                            ?? ih `at` (Inst @"bs" bs, Inst @"cs" cs)
                                            =: ite (a `elem` (bs ++ cs)) ((as \\ bs) \\ cs) (a .: (as \\ (bs ++ cs)))
                                            ?? ih `at` (Inst @"bs" bs, Inst @"cs" cs)
                                            =: ite (a `elem` (bs ++ cs)) ((as \\ bs) \\ cs) (a .: ((as \\ bs) \\ cs))
                                            =: ((a .: as) \\ bs) \\ cs
                                            =: qed

-- | @(as \\ bs) \\ cs == (as \\ cs) \\ bs@
--
-- >>> runTP $ diffDiff @Integer
-- Inductive lemma: diffDiff
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
-- [Proven] diffDiff :: Ɐas ∷ [Integer] → Ɐbs ∷ [Integer] → Ɐcs ∷ [Integer] → Bool
diffDiff :: forall a. (Eq a, SymVal a) => TP (Proof (Forall "as" [a] -> Forall "bs" [a] -> Forall "cs" [a] -> SBool))
diffDiff = induct "diffDiff"
                  (\(Forall as) (Forall bs) (Forall cs) -> (as \\ bs) \\ cs .== (as \\ cs) \\ bs) $
                  \ih (a, as) bs cs ->
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

-- | Are the two lists disjoint?
disjoint :: (Eq a, SymVal a) => SList a -> SList a -> SBool
disjoint = smtFunction "disjoint" $ \xs ys -> null xs .|| head xs `notElem` ys .&& disjoint (tail xs) ys

-- | @disjoint as bs .=> as \\ bs == as@
--
-- >>> runTP $ disjointDiff @Integer
-- Inductive lemma: disjointDiff
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] disjointDiff :: Ɐas ∷ [Integer] → Ɐbs ∷ [Integer] → Bool
disjointDiff :: forall a. (Eq a, SymVal a) => TP (Proof (Forall "as" [a] -> Forall "bs" [a] -> SBool))
disjointDiff = induct "disjointDiff"
                      (\(Forall as) (Forall bs) -> disjoint as bs .=> as \\ bs .== as) $
                      \ih (a, as) bs -> [disjoint (a .: as) bs]
                                     |- (a .: as) \\ bs
                                     =: a .: (as \\ bs)
                                     ?? ih
                                     =: a .: as
                                     =: qed

-- | @fst (partition f xs) == filter f xs@
--
-- >>> runTP $ partition1 @Integer (uninterpret "f")
-- Inductive lemma: partition1
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] partition1 :: Ɐxs ∷ [Integer] → Bool
partition1 :: forall a. SymVal a => (SBV a -> SBool) -> TP (Proof (Forall "xs" [a] -> SBool))
partition1 f =
   induct "partition1"
          (\(Forall xs) -> fst (partition f xs) .== filter f xs) $
          \ih (x, xs) -> [] |- fst (partition f (x .: xs))
                            =: fst (let res = partition f xs
                                    in ite (f x)
                                           (tuple (x .: fst res, snd res))
                                           (tuple (fst res, x .: snd res)))
                            =: ite (f x) (x .: fst (partition f xs)) (fst (partition f xs))
                            ?? ih
                            =: ite (f x) (x .: filter f xs) (filter f xs)
                            =: filter f (x .: xs)
                            =: qed

-- | @snd (partition f xs) == filter (not . f) xs@
--
-- >>> runTP $ partition2 @Integer (uninterpret "f")
-- Inductive lemma: partition2
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] partition2 :: Ɐxs ∷ [Integer] → Bool
partition2 :: forall a. SymVal a => (SBV a -> SBool) -> TP (Proof (Forall "xs" [a] -> SBool))
partition2 f =
   induct "partition2"
          (\(Forall xs) -> snd (partition f xs) .== filter (sNot . f) xs) $
          \ih (x, xs) -> [] |- snd (partition f (x .: xs))
                            =: snd (let res = partition f xs
                                    in ite (f x)
                                           (tuple (x .: fst res, snd res))
                                           (tuple (fst res, x .: snd res)))
                            =: ite (f x) (snd (partition f xs)) (x .: snd (partition f xs))
                            ?? ih
                            =: ite (f x) (filter (sNot . f) xs) (x .: filter (sNot . f) xs)
                            =: filter (sNot . f) (x .: xs)
                            =: qed

-- | @take n (take m xs) == take (n `smin` m) xs@
--
-- >>> runTP $ take_take @Integer
-- Lemma: take_take                        Q.E.D.
-- [Proven] take_take :: Ɐm ∷ Integer → Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
take_take :: forall a. SymVal a => TP (Proof (Forall "m" Integer -> Forall "n" Integer -> Forall "xs" [a] -> SBool))
take_take = lemma "take_take"
                  (\(Forall m) (Forall n) (Forall xs) -> take n (take m xs) .== take (n `smin` m) xs)
                  []

-- | @n >= 0 && m >= 0 ==> drop n (drop m xs) == drop (n + m) xs@
--
-- >>> runTP $ drop_drop @Integer
-- Lemma: drop_drop                        Q.E.D.
-- [Proven] drop_drop :: Ɐm ∷ Integer → Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
drop_drop :: forall a. SymVal a => TP (Proof (Forall "m" Integer -> Forall "n" Integer -> Forall "xs" [a] -> SBool))
drop_drop = lemma "drop_drop"
                  (\(Forall m) (Forall n) (Forall xs) -> n .>= 0 .&& m .>= 0 .=> drop n (drop m xs) .== drop (n + m) xs)
                  []

-- | @take n xs ++ drop n xs == xs@
--
-- >>> runTP $ take_drop @Integer
-- Lemma: take_drop                        Q.E.D.
-- [Proven] take_drop :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
take_drop :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> SBool))
take_drop = lemma "take_drop"
                  (\(Forall n) (Forall xs) -> take n xs ++ drop n xs .== xs)
                  []

-- | @n .> 0 ==> take n (x .: xs) == x .: take (n - 1) xs@
--
-- >>> runTP $ take_cons @Integer
-- Lemma: take_cons                        Q.E.D.
-- [Proven] take_cons :: Ɐn ∷ Integer → Ɐx ∷ Integer → Ɐxs ∷ [Integer] → Bool
take_cons :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "x" a -> Forall "xs" [a] -> SBool))
take_cons = lemma "take_cons"
                  (\(Forall n) (Forall x) (Forall xs) -> n .> 0 .=> take n (x .: xs) .== x .: take (n - 1) xs)
                  []

-- | @take n (map f xs) == map f (take n xs)@
--
-- >>> runTP $ take_map @Integer @Float (uninterpret "f")
-- Lemma: take_cons                        Q.E.D.
-- Lemma: map1                             Q.E.D.
-- Lemma: take_map.n <= 0                  Q.E.D.
-- Inductive lemma: take_map.n > 0
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: take_map                         Q.E.D.
-- [Proven] take_map :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
take_map :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> SBool))
take_map f = do
    tc   <- take_cons @a

    map1 <- lemma "map1"
                  (\(Forall x) (Forall xs) -> map f (x .: xs) .== f x .: map f xs)
                  []

    h1 <- lemma "take_map.n <= 0"
                 (\(Forall @"xs" xs) (Forall @"n" n) -> n .<= 0 .=> take n (map f xs) .== map f (take n xs))
                 []

    h2 <- induct "take_map.n > 0"
                 (\(Forall @"xs" xs) (Forall @"n" n) -> n .> 0 .=> take n (map f xs) .== map f (take n xs)) $
                 \ih (x, xs) n -> [n .> 0] |- take n (map f (x .: xs))
                                           =: take n (f x .: map f xs)
                                           =: f x .: take (n - 1) (map f xs)
                                           ?? ih `at` Inst @"n" (n-1)
                                           =: f x .: map f (take (n - 1) xs)
                                           ?? map1 `at` (Inst @"x" x, Inst @"xs" (take (n - 1) xs))
                                           =: map f (x .: take (n - 1) xs)
                                           ?? tc
                                           =: map f (take n (x .: xs))
                                           =: qed

    lemma "take_map"
          (\(Forall n) (Forall xs) -> take n (map f xs) .== map f (take n xs))
          [proofOf h1, proofOf h2]

-- | @n .> 0 ==> drop n (x .: xs) == drop (n - 1) xs@
--
-- >>> runTP $ drop_cons @Integer
-- Lemma: drop_cons                        Q.E.D.
-- [Proven] drop_cons :: Ɐn ∷ Integer → Ɐx ∷ Integer → Ɐxs ∷ [Integer] → Bool
drop_cons :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "x" a -> Forall "xs" [a] -> SBool))
drop_cons = lemma "drop_cons"
                  (\(Forall n) (Forall x) (Forall xs) -> n .> 0 .=> drop n (x .: xs) .== drop (n - 1) xs)
                  []

-- | @drop n (map f xs) == map f (drop n xs)@
--
-- >>> runTP $ drop_map @Integer @String (uninterpret "f")
-- Lemma: drop_cons                        Q.E.D.
-- Lemma: drop_cons                        Q.E.D.
-- Lemma: drop_map.n <= 0                  Q.E.D.
-- Inductive lemma: drop_map.n > 0
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: drop_map
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] drop_map :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
drop_map :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> SBool))
drop_map f = do
   dcA <- drop_cons @a
   dcB <- drop_cons @b

   h1 <- lemma "drop_map.n <= 0"
               (\(Forall @"xs" xs) (Forall @"n" n) -> n .<= 0 .=> drop n (map f xs) .== map f (drop n xs))
               []

   h2 <- induct "drop_map.n > 0"
                (\(Forall @"xs" xs) (Forall @"n" n) -> n .> 0 .=> drop n (map f xs) .== map f (drop n xs)) $
                \ih (x, xs) n -> [n .> 0] |- drop n (map f (x .: xs))
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
   calc "drop_map"
        (\(Forall n) (Forall xs) -> drop n (map f xs) .== map f (drop n xs)) $
        \n xs -> [] |- let result = drop n (map f xs) .== map f (drop n xs)
                       in result
                       =: ite (n .<= 0) (n .<= 0 .=> result) (n .> 0 .=> result)
                       ?? h1
                       =: ite (n .<= 0) sTrue (n .> 0 .=> result)
                       ?? h2
                       =: ite (n .<= 0) sTrue sTrue
                       =: sTrue
                       =: qed

-- | @n >= 0 ==> length (take n xs) == length xs \`min\` n@
--
-- >>> runTP $ length_take @Integer
-- Lemma: length_take                      Q.E.D.
-- [Proven] length_take :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
length_take :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> SBool))
length_take = lemma "length_take"
                    (\(Forall n) (Forall xs) -> n .>= 0 .=> length (take n xs) .== length xs `smin` n)
                    []

-- | @n >= 0 ==> length (drop n xs) == (length xs - n) \`max\` 0@
--
-- >>> runTP $ length_drop @Integer
-- Lemma: length_drop                      Q.E.D.
-- [Proven] length_drop :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
length_drop :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> SBool))
length_drop = lemma "length_drop"
                    (\(Forall n) (Forall xs) -> n .>= 0 .=> length (drop n xs) .== (length xs - n) `smax` 0)
                    []

-- | @length xs \<= n ==\> take n xs == xs@
--
-- >>> runTP $ take_all @Integer
-- Lemma: take_all                         Q.E.D.
-- [Proven] take_all :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
take_all :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> SBool))
take_all = lemma "take_all"
                 (\(Forall n) (Forall xs) -> length xs .<= n .=> take n xs .== xs)
                 []

-- | @length xs \<= n ==\> drop n xs == nil@
--
-- >>> runTP $ drop_all @Integer
-- Lemma: drop_all                         Q.E.D.
-- [Proven] drop_all :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Bool
drop_all :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> SBool))
drop_all = lemma "drop_all"
                 (\(Forall n) (Forall xs) -> length xs .<= n .=> drop n xs .== nil)
                 []

-- | @take n (xs ++ ys) == (take n xs ++ take (n - length xs) ys)@
--
-- >>> runTP $ take_append @Integer
-- Lemma: take_append                      Q.E.D.
-- [Proven] take_append :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
take_append :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> Forall "ys" [a] -> SBool))
take_append = lemmaWith cvc5 "take_append"
                        (\(Forall n) (Forall xs) (Forall ys) -> take n (xs ++ ys) .== take n xs ++ take (n - length xs) ys)
                        []

-- | @drop n (xs ++ ys) == drop n xs ++ drop (n - length xs) ys@
--
-- NB. As of Feb 2025, z3 struggles to prove this, but cvc5 gets it out-of-the-box.
--
-- >>> runTP $ drop_append @Integer
-- Lemma: drop_append                      Q.E.D.
-- [Proven] drop_append :: Ɐn ∷ Integer → Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
drop_append :: forall a. SymVal a => TP (Proof (Forall "n" Integer -> Forall "xs" [a] -> Forall "ys" [a] -> SBool))
drop_append = lemmaWith cvc5 "drop_append"
                        (\(Forall n) (Forall xs) (Forall ys) -> drop n (xs ++ ys) .== drop n xs ++ drop (n - length xs) ys)
                        []

-- | @length xs == length ys ==> map fst (zip xs ys) = xs@
--
-- >>> runTP $ map_fst_zip @Integer @Integer
-- Inductive lemma: map_fst_zip
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_fst_zip :: (Ɐxs ∷ [Integer], Ɐys ∷ [Integer]) → Bool
map_fst_zip :: forall a b. (SymVal a, SymVal b) => TP (Proof ((Forall "xs" [a], Forall "ys" [b]) -> SBool))
map_fst_zip = induct "map_fst_zip"
                     (\(Forall xs, Forall ys) -> length xs .== length ys .=> map fst (zip xs ys) .== xs) $
                     \ih (x, xs, y, ys) -> [length (x .: xs) .== length (y .: ys)]
                                        |- map fst (zip (x .: xs) (y .: ys))
                                        =: map fst (tuple (x, y) .: zip xs ys)
                                        =: fst (tuple (x, y)) .: map fst (zip xs ys)
                                        =: x .: map fst (zip xs ys)
                                        ?? ih
                                        =: x .: xs
                                        =: qed

-- | @length xs == length ys ==> map snd (zip xs ys) = xs@
--
-- >>> runTP $ map_snd_zip @Integer @Integer
-- Inductive lemma: map_snd_zip
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_snd_zip :: (Ɐxs ∷ [Integer], Ɐys ∷ [Integer]) → Bool
map_snd_zip :: forall a b. (SymVal a, SymVal b) => TP (Proof ((Forall "xs" [a], Forall "ys" [b]) -> SBool))
map_snd_zip = induct "map_snd_zip"
                     (\(Forall xs, Forall ys) -> length xs .== length ys .=> map snd (zip xs ys) .== ys) $
                     \ih (x, xs, y, ys) -> [length (x .: xs) .== length (y .: ys)]
                                        |- map snd (zip (x .: xs) (y .: ys))
                                        =: map snd (tuple (x, y) .: zip xs ys)
                                        =: snd (tuple (x, y)) .: map snd (zip xs ys)
                                        =: y .: map snd (zip xs ys)
                                        ?? ih
                                        =: y .: ys
                                        =: qed

-- | @map fst (zip xs ys) == take (min (length xs) (length ys)) xs@
--
-- >>> runTP $ map_fst_zip_take @Integer @Integer
-- Lemma: take_cons                        Q.E.D.
-- Inductive lemma: map_fst_zip_take
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_fst_zip_take :: (Ɐxs ∷ [Integer], Ɐys ∷ [Integer]) → Bool
map_fst_zip_take :: forall a b. (SymVal a, SymVal b) => TP (Proof ((Forall "xs" [a], Forall "ys" [b]) -> SBool))
map_fst_zip_take = do
   tc <- take_cons @a

   induct "map_fst_zip_take"
          (\(Forall xs, Forall ys) -> map fst (zip xs ys) .== take (length xs `smin` length ys) xs) $
          \ih (x, xs, y, ys) -> [] |- map fst (zip (x .: xs) (y .: ys))
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
-- >>> runTP $ map_snd_zip_take @Integer @Integer
-- Lemma: take_cons                        Q.E.D.
-- Inductive lemma: map_snd_zip_take
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_snd_zip_take :: (Ɐxs ∷ [Integer], Ɐys ∷ [Integer]) → Bool
map_snd_zip_take :: forall a b. (SymVal a, SymVal b) => TP (Proof ((Forall "xs" [a], Forall "ys" [b]) -> SBool))
map_snd_zip_take = do
   tc <- take_cons @a

   induct "map_snd_zip_take"
          (\(Forall xs, Forall ys) -> map snd (zip xs ys) .== take (length xs `smin` length ys) ys) $
          \ih (x, xs, y, ys) -> [] |- map snd (zip (x .: xs) (y .: ys))
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

-- | Interleave the elements of two lists. If one ends, we take the rest from the other.
interleave :: SymVal a => SList a -> SList a -> SList a
interleave = smtFunction "interleave" (\xs ys -> ite (null  xs) ys (head xs .: interleave ys (tail xs)))

-- | Prove that interleave preserves total length.
--
-- The induction here is on the total length of the lists, and hence
-- we use the generalized induction principle. We have:
--
-- >>> runTP $ interleaveLen @Integer
-- Inductive lemma (strong): interleaveLen
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] interleaveLen :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
interleaveLen :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
interleaveLen = sInduct "interleaveLen"
                        (\(Forall xs) (Forall ys) -> length xs + length ys .== length (interleave xs ys))
                        (\xs ys -> length xs + length ys) $
                        \ih xs ys -> [] |- length xs + length ys .== length (interleave xs ys)
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
-- >>> runTP $ interleaveRoundTrip @Integer
-- Lemma: revCons                          Q.E.D.
-- Inductive lemma (strong): roundTripGen
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
-- Lemma: interleaveRoundTrip
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] interleaveRoundTrip :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Bool
interleaveRoundTrip :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
interleaveRoundTrip = do

   revHelper <- lemma "revCons" (\(Forall a) (Forall as) (Forall bs) -> reverse @a (a .: as) ++ bs .== reverse as ++ (a .: bs)) []

   -- Generalize the theorem first to take the helper lists explicitly
   roundTripGen <- sInductWith cvc5
         "roundTripGen"
         (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"alts" alts) ->
               length xs .== length ys .=> let (es, os) = untuple alts
                                           in uninterleaveGen (interleave xs ys) alts .== tuple (reverse es ++ xs, reverse os ++ ys))
         (\xs ys _alts -> length xs + length ys) $
         \ih xs ys alts -> [length xs .== length ys]
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
   calc "interleaveRoundTrip"
           (\(Forall xs) (Forall ys) -> length xs .== length ys .=> uninterleave (interleave xs ys) .== tuple (xs, ys)) $
           \xs ys -> [length xs .== length ys]
                  |- uninterleave (interleave xs ys)
                  =: uninterleaveGen (interleave xs ys) (tuple (nil, nil))
                  ?? roundTripGen `at` (Inst @"xs" xs, Inst @"ys" ys, Inst @"alts" (tuple (nil, nil)))
                  =: tuple (reverse nil ++ xs, reverse nil ++ ys)
                  =: qed

-- | @count e (xs ++ ys) == count e xs + count e ys@
--
-- >>> runTP $ countAppend @Integer
-- Inductive lemma: countAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold count)                Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (simplify)                    Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countAppend :: Ɐxs ∷ [Integer] → Ɐys ∷ [Integer] → Ɐe ∷ Integer → Bool
countAppend :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> Forall "e" a -> SBool))
countAppend =
   induct "countAppend"
          (\(Forall xs) (Forall ys) (Forall e) -> count e (xs ++ ys) .== count e xs + count e ys) $
          \ih (x, xs) ys e -> [] |- count e ((x .: xs) ++ ys)
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
-- >>> runTP $ takeDropCount @Integer
-- Inductive lemma: countAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold count)                Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (simplify)                    Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: take_drop                        Q.E.D.
-- Lemma: takeDropCount
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] takeDropCount :: Ɐxs ∷ [Integer] → Ɐn ∷ Integer → Ɐe ∷ Integer → Bool
takeDropCount :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "n" Integer -> Forall "e" a -> SBool))
takeDropCount = do
       capp     <- countAppend @a
       takeDrop <- take_drop   @a

       calc "takeDropCount"
            (\(Forall xs) (Forall n) (Forall e) -> count e (take n xs) + count e (drop n xs) .== count e xs) $
            \xs n e -> [] |- count e (take n xs) + count e (drop n xs)
                          ?? capp `at` (Inst @"xs" (take n xs), Inst @"ys" (drop n xs), Inst @"e" e)
                          =: count e (take n xs ++ drop n xs)
                          ?? takeDrop
                          =: count e xs
                          =: qed

-- | @count e xs >= 0@
--
-- >>> runTP $ countNonNeg @Integer
-- Inductive lemma: countNonNeg
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countNonNeg :: Ɐxs ∷ [Integer] → Ɐe ∷ Integer → Bool
countNonNeg :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> Forall "e" a -> SBool))
countNonNeg =
   induct "countNonNeg"
          (\(Forall xs) (Forall e) -> count e xs .>= 0) $
          \ih (x, xs) e -> [] |- count e (x .: xs) .>= 0
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
-- >>> runTP $ countElem @Integer
-- Inductive lemma: countNonNeg
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: countElem
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countElem :: Ɐxs ∷ [Integer] → Ɐe ∷ Integer → Bool
countElem :: forall a. (Eq a, SymVal a) => TP (Proof (Forall "xs" [a] -> Forall "e" a -> SBool))
countElem = do

    cnn <- countNonNeg @a

    induct "countElem"
           (\(Forall xs) (Forall e) -> e `elem` xs .=> count e xs .> 0) $
           \ih (x, xs) e -> [e `elem` (x .: xs)]
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
-- >>> runTP $ elemCount @Integer
-- Inductive lemma: elemCount
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] elemCount :: Ɐxs ∷ [Integer] → Ɐe ∷ Integer → Bool
elemCount :: forall a. (Eq a, SymVal a) => TP (Proof (Forall "xs" [a] -> Forall "e" a -> SBool))
elemCount =
    induct "elemCount"
           (\(Forall xs) (Forall e) -> count e xs .> 0 .=> e `elem` xs) $
           \ih (x, xs) e -> [count e xs .> 0]
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
{- HLint ignore tailsAppend    "Avoid lambda"      -}
{- HLint ignore tailsAppend    "Use :"             -}
{- HLint ignore mapReverse     "Evaluate"          -}
{- HLint ignore takeDropWhile  "Evaluate"          -}
