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
     appendNull, consApp, appendAssoc

     -- * Reverse
   , revLen, revApp, revCons, revSnoc, revRev

     -- * Length
   , lengthTail, lenAppend, lenAppend2

     -- * Replicate
   , replicateLength

     -- * All and any
   , allAny

     -- * Map
   , mapEquiv, mapAppend, mapReverse

     -- * Foldr and foldl
   , foldrMapFusion, foldrFusion, foldrOverAppend, foldlOverAppend, foldrFoldlDuality, foldrFoldlDualityGeneralized, foldrFoldl
   , bookKeeping

     -- * Filter
   , filterAppend, filterConcat, mapFilter

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
   , count, countAppend, takeDropCount, countNonNegative, countElem, elemCount
 ) where

import Prelude (Eq, IO, ($), Num(..), id, (.), flip)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.Tools.TP

import Control.Monad (void)
import Data.Proxy

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.Proxy
-- >>> import Control.Exception
#endif

-- * Appending null

-- | @xs ++ [] == xs@
--
-- >>> appendNull (Proxy @Integer)
-- Lemma: appendNull @Integer              Q.E.D.
-- [Proven] appendNull @Integer
appendNull :: forall a. SymVal a => Proxy a -> IO Proof
appendNull p = runTP $ lemma (atProxy p "appendNull")
                             (\(Forall @"xs" (xs :: SList a)) -> xs ++ nil .== xs)
                             []

-- * Moving cons over append

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- >>> consApp (Proxy @Integer)
-- Lemma: consApp @Integer                 Q.E.D.
-- [Proven] consApp @Integer
consApp :: forall a. SymVal a => Proxy a -> IO Proof
consApp p = runTP $ lemma (atProxy p "consApp") (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys)) []

-- * Associativity of append

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- >>> appendAssoc (Proxy @Integer)
-- Lemma: appendAssoc @Integer             Q.E.D.
-- [Proven] appendAssoc @Integer
--
-- Surprisingly, z3 can prove this without any induction. (Since SBV's append translates directly to
-- the concatenation of sequences in SMTLib, it must trigger an internal heuristic in z3
-- that proves it right out-of-the-box!)
appendAssoc :: forall a. SymVal a => Proxy a -> IO Proof
appendAssoc p = runTP $
   lemma (atProxy p "appendAssoc") (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) (Forall @"zs" zs) -> xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs) []

-- * Reverse

-- | @length xs == length (reverse xs)@
--
-- >>> revLen (Proxy @Integer)
-- Inductive lemma: revLen @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revLen @Integer
revLen :: forall a. SymVal a => Proxy a -> IO Proof
revLen p = runTP $
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
-- >>> revApp (Proxy @Integer)
-- Inductive lemma: revApp @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revApp @Integer
revApp :: forall a. SymVal a => Proxy a -> IO Proof
revApp p = runTP $
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
-- >>> revCons (Proxy @Integer)
-- Lemma: revCons @Integer                 Q.E.D.
-- [Proven] revCons @Integer
revCons :: forall a. SymVal a => Proxy a -> IO Proof
revCons p = runTP $ lemma (atProxy p "revCons") (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) -> reverse (x .: xs) .== reverse xs ++ singleton x) []

-- | @reverse (xs ++ [x]) == x : reverse xs@
--
-- >>> revSnoc (Proxy @Integer)
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
revSnoc :: forall a. SymVal a => Proxy a -> IO Proof
revSnoc p = runTP $ do
   ra <- use $ revApp p

   lemma (atProxy p "revSnoc")
         (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) -> reverse (xs ++ singleton x) .== x .: reverse xs)
         [ra]

-- * Reversing twice is identity

-- | @reverse (reverse xs) == xs@
--
-- >>> revRev (Proxy @Integer)
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
revRev :: forall a. SymVal a => Proxy a -> IO Proof
revRev p = runTP $ do

   ra <- use $ revApp p

   induct (atProxy p "revRev")
          (\(Forall @"xs" (xs :: SList a)) -> reverse (reverse xs) .== xs) $
          \ih (x :: SBV a) xs -> [] |- reverse (reverse (x .: xs))
                                    =: reverse (reverse xs ++ singleton x)           ?? ra
                                    =: reverse (singleton x) ++ reverse (reverse xs) ?? ih
                                    =: singleton x ++ xs
                                    =: x .: xs
                                    =: qed

-- * Lengths of lists

-- | @length (x : xs) == 1 + length xs@
--
-- >>> lengthTail (Proxy @Integer)
-- Lemma: lengthTail @Integer              Q.E.D.
-- [Proven] lengthTail @Integer
lengthTail :: forall a. SymVal a => Proxy a -> IO Proof
lengthTail p = runTP $
   lemma (atProxy p "lengthTail")
         (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) -> length (x .: xs) .== 1 + length xs)
         []

-- | @length (xs ++ ys) == length xs + length ys@
--
-- >>> lenAppend (Proxy @Integer)
-- Lemma: lenAppend @Integer               Q.E.D.
-- [Proven] lenAppend @Integer
lenAppend :: forall a. SymVal a => Proxy a -> IO Proof
lenAppend p = runTP $
   lemma (atProxy p "lenAppend")
         (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> length (xs ++ ys) .== length xs + length ys)
         []

-- | @length xs == length ys -> length (xs ++ ys) == 2 * length xs@
--
-- >>> lenAppend2 (Proxy @Integer)
-- Lemma: lenAppend2 @Integer              Q.E.D.
-- [Proven] lenAppend2 @Integer
lenAppend2 :: forall a. SymVal a => Proxy a -> IO Proof
lenAppend2 p = runTP $
    lemma (atProxy p "lenAppend2")
          (\(Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> length xs .== length ys .=> length (xs ++ ys) .== 2 * length xs)
          []

-- * Replicate

-- | @length (replicate k x) == max (0, k)@
--
-- >>> replicateLength (Proxy @Integer)
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
replicateLength :: forall a. SymVal a => Proxy a -> IO Proof
replicateLength p = runTP $
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

-- * Any, all, and filtering

-- | @not (all id xs) == any not xs@
--
-- A list of booleans is not all true, if any of them is false.
--
-- >>> allAny
-- Inductive lemma: allAny
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] allAny
allAny :: IO Proof
allAny = runTP $
   induct "allAny"
          (\(Forall @"xs" xs) -> sNot (all id xs) .== any sNot xs) $
          \ih x xs -> [] |- sNot (all id (x .: xs))
                         =: sNot (x .&& all id xs)
                         =: (sNot x .|| sNot (all id xs))   ?? ih
                         =: sNot x .|| any sNot xs
                         =: any sNot (x .: xs)
                         =: qed

-- * Map, append, and reverse

-- | @f == g ==> map f xs == map g xs@
--
-- >>> mapEquiv @Integer @Integer (uninterpret "f") (uninterpret "g")
-- Inductive lemma: mapEquiv @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapEquiv @(Integer,Integer)
mapEquiv :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> (SBV a -> SBV b) -> IO Proof
mapEquiv f g = runTP $ do
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
-- >>> mapAppend @Integer @Integer (uninterpret "f")
-- Inductive lemma: mapAppend @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mapAppend @(Integer,Integer)
mapAppend :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> IO Proof
mapAppend f = runTP $ do
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
-- >>> mapReverse @Integer @String (uninterpret "f")
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
mapReverse :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> IO Proof
mapReverse f = runTP $ do
     mApp <- use (mapAppend f)

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

-- * Foldr-map fusion

-- | @foldr f a . map g == foldr (f . g) a@
--
-- >>> foldrMapFusion @Integer @Bool @String (uninterpret "a") (uninterpret "b") (uninterpret "c")
-- Inductive lemma: foldrMapFusion @(Integer,Bool,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrMapFusion @(Integer,Bool,[Char])
foldrMapFusion :: forall a b c. (SymVal a, SymVal b, SymVal c) => SBV a -> (SBV c -> SBV b) -> (SBV b -> SBV a -> SBV a) -> IO Proof
foldrMapFusion a g f = runTP $ do
  induct (atProxy (Proxy @(a, b, c)) "foldrMapFusion")
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
--   f . foldr g a == foldr h b
--   provided, f a = b and for all x and y, f (g x y) == h x (f y).
-- @
--
-- >>> foldrFusion @Integer @Bool @String (uninterpret "a") (uninterpret "b") (uninterpret "f") (uninterpret "g") (uninterpret "h")
-- Inductive lemma: foldrFusion @(Integer,Bool,[Char])
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrFusion @(Integer,Bool,[Char])
foldrFusion :: forall a b c. (SymVal a, SymVal b, SymVal c) => SBV a -> SBV b -> (SBV a -> SBV b) -> (SBV c -> SBV a -> SBV a) -> (SBV c -> SBV b -> SBV b) -> IO Proof
foldrFusion a b f g h = runTP $ do
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

-- * Foldr over append

-- | @foldr f a (xs ++ ys) == foldr f (foldr f a ys) xs@
--
-- >>> foldrOverAppend @Integer (uninterpret "a") (uninterpret "f")
-- Inductive lemma: foldrOverAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldrOverAppend @Integer
foldrOverAppend :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> IO Proof
foldrOverAppend a f = runTP $ do
   induct (atProxy (Proxy @a) "foldrOverAppend")
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
-- >>> foldlOverAppend @Integer @Bool (uninterpret "f")
-- Inductive lemma: foldlOverAppend @(Integer,Bool)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] foldlOverAppend @(Integer,Bool)
foldlOverAppend :: forall a b. (SymVal a, SymVal b) => (SBV b -> SBV a -> SBV b) -> IO Proof
foldlOverAppend f = runTP $
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

-- * Foldr-foldl correspondence

-- | @foldr f e xs == foldl (flip f) e (reverse xs)@
--
-- >>> foldrFoldlDuality @Integer @String (uninterpret "f")
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
foldrFoldlDuality :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> IO Proof
foldrFoldlDuality f = runTP $ do
   foa <- use (foldlOverAppend (flip f))

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

-- * Foldr-foldl duality, generalized

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
-- >>> foldrFoldlDualityGeneralized @Integer (uninterpret "e") (uninterpret "|@|")
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
foldrFoldlDualityGeneralized :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> IO Proof
foldrFoldlDualityGeneralized  e (@) = runTP $ do
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
-- In Bird's Introduction to Functional Programming book (2nd edition) this is called the second duality theorem:
--
-- >>> foldrFoldl @Integer @String (uninterpret "<+>") (uninterpret "<*>") (uninterpret "e")
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
foldrFoldl :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> (SBV b -> SBV a -> SBV b) -> SBV b-> IO Proof
foldrFoldl (<+>) (<*>) e = runTP $ do
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

-- * Bookkeeping law

-- | Provided @f@ is associative and @a@ is its both left and right-unit:
--
-- @foldr f a . concat == foldr f a . map (foldr f a)@
--
-- >>> bookKeeping @Integer (uninterpret "a") (uninterpret "f")
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
bookKeeping :: forall a. SymVal a => SBV a -> (SBV a -> SBV a -> SBV a) -> IO Proof
bookKeeping a f = runTP $ do
   let -- Fuse map (foldr f a) in the theorem into one call to avoid nested lambdas. See above note.
       mapFoldr :: SBV a -> SList [a] -> SList a
       mapFoldr = smtFunction "mapFoldr" $ \e xss -> ite (null xss)
                                                         nil
                                                         (foldr f e (head xss) .: mapFoldr e (tail xss))

   -- Assumptions about f
   let assoc = quantifiedBool $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x `f` (y `f` z) .== (x `f` y) `f` z
       rUnit = quantifiedBool $ \(Forall @"x" x) -> x `f` a .== x
       lUnit = quantifiedBool $ \(Forall @"x" x) -> a `f` x .== x

   -- Helper:
   --   foldr f y xs = foldr f a xs `f` y
   helper <- induct (atProxy (Proxy @a) "foldBase")
                    (\(Forall @"xs" xs) (Forall @"y" y) -> lUnit .&& assoc .=> foldr f y xs .== foldr f a xs `f` y) $
                    \ih x xs y -> [lUnit, assoc] |- foldr f y (x .: xs)
                                                 =: x `f` foldr f y xs          ?? ih
                                                 =: x `f` (foldr f a xs `f` y)
                                                 =: (x `f` foldr f a xs) `f` y
                                                 =: foldr f a (x .: xs) `f` y
                                                 =: qed

   foa <- use $ foldrOverAppend a f

   induct (atProxy (Proxy @a) "bookKeeping")
          (\(Forall @"xss" xss) -> assoc .&& rUnit .&& lUnit .=> foldr f a (concat xss) .== foldr f a (mapFoldr a xss)) $
          \ih xs xss -> [assoc, rUnit, lUnit] |- foldr f a (concat (xs .: xss))
                                              =: foldr f a (xs ++ concat xss)
                                              ?? foa
                                              =: foldr f (foldr f a (concat xss)) xs
                                              ?? ih
                                              =: foldr f (foldr f a (mapFoldr a xss)) xs
                                              ?? helper `at` (Inst @"xs" xs, Inst @"y" (foldr f a (mapFoldr a xss)))
                                              =: foldr f a xs `f` foldr f a (mapFoldr a xss)
                                              =: foldr f a (foldr f a xs .: mapFoldr a xss)
                                              =: foldr f a (mapFoldr a (xs .: xss))
                                              =: qed

-- * Filter-append

-- | @filter p (xs ++ ys) == filter p xs ++ filter p ys@
--
-- >>> filterAppend @Integer (uninterpret "p")
-- Inductive lemma: filterAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] filterAppend @Integer
filterAppend :: forall a. SymVal a => (SBV a -> SBool) -> IO Proof
filterAppend p = runTP $
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
-- Similar to the book-keeping law, we cannot express this in SBV directly, since it involves a nested lambda.
-- @concatMap (filter p)@ maps a higher-order function @filter p@, which itself has a nested lambda. So, we use
-- our own merged definition. Hopefully we'll relax this as SMTLib gains more higher order features.
--
-- >>> filterConcat @Integer (uninterpret "f")
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
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] filterConcat @Integer
filterConcat :: forall a. SymVal a => (SBV a -> SBool) -> IO Proof
filterConcat p = runTP $ do
  let -- Fuse concatMap (filter p) in the theorem to avoid nested lambdas. See above note
      concatMapFilter :: SymVal a => (SBV a -> SBool) -> SList [a] -> SList a
      concatMapFilter pred = smtFunction "concatMapFilter" $ \xs -> ite (null xs)
                                                                        nil
                                                                        (filter pred (head xs) ++ concatMapFilter pred (tail xs))


  fa <- use $ filterAppend p

  induct (atProxy (Proxy @a) "filterConcat")
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
-- >>> mapFilter @Integer (uninterpret "f") (uninterpret "p") `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badMapFilter
-- *** Failed to prove badMapFilter.
-- Falsifiable. Counter-example:
--   xs  = [9] :: [Integer]
--   lhs = [2] :: [Integer]
--   rhs =  [] :: [Integer]
-- <BLANKLINE>
--   f :: Integer -> Integer
--   f _ = 2
-- <BLANKLINE>
--   p :: Integer -> Bool
--   p 9 = True
--   p _ = False
--
-- As expected, the function @f@ maps everything to @2@, and the predicate @p@ only lets @9@ through. As shown in the
-- counter-example, for the input @[9]@, left-hand-side filters nothing and the result is the singleton @20@. But the
-- map on the right-hand side maps everything to @[2]@ and the filter gets rid of the elements, resulting in an empty list.
mapFilter :: SymVal a => (SBV a -> SBV a) -> (SBV a -> SBool) -> IO ()
mapFilter f p = runTP $
   void $ lemma "badMapFilter"
                (\(Forall @"xs" xs) -> observe "lhs" (map f (filter p xs)) .== observe "rhs" (filter p (map f xs)))
                []

-- * Partition

-- | @fst (partition f xs) == filter f xs@
--
-- >>> partition1 @Integer (uninterpret "f")
-- Inductive lemma: partition1 @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] partition1 @Integer
partition1 :: forall a. SymVal a => (SBV a -> SBool) -> IO Proof
partition1 f = runTP $
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
-- >>> partition2 @Integer (uninterpret "f")
-- Inductive lemma: partition2 @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] partition2 @Integer
partition2 :: forall a. SymVal a => (SBV a -> SBool) -> IO Proof
partition2 f = runTP $
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

-- * Take and drop

-- | @take n (take m xs) == take (n `smin` m) xs@
--
-- >>> take_take (Proxy @Integer)
-- Lemma: take_take @Integer               Q.E.D.
-- [Proven] take_take @Integer
take_take :: forall a. SymVal a => Proxy a -> IO Proof
take_take p = runTP $
   lemma (atProxy p "take_take")
         (\(Forall @"xs" (xs :: SList a)) (Forall @"m" m) (Forall @"n" n) -> take n (take m xs) .== take (n `smin` m) xs)
         []


-- | @n >= 0 && m >= 0 ==> drop n (drop m xs) == drop (n + m) xs@
--
-- >>> drop_drop (Proxy @Integer)
-- Lemma: drop_drop @Integer               Q.E.D.
-- [Proven] drop_drop @Integer
drop_drop :: forall a. SymVal a => Proxy a -> IO Proof
drop_drop p = runTP $
   lemma (atProxy p "drop_drop")
          (\(Forall @"n" n) (Forall @"m" m) (Forall @"xs" (xs :: SList a)) ->
                n .>= 0 .&& m .>= 0 .=> drop n (drop m xs) .== drop (n + m) xs)
          []

-- | @take n xs ++ drop n xs == xs@
--
-- >>> take_drop (Proxy @Integer)
-- Lemma: take_drop @Integer               Q.E.D.
-- [Proven] take_drop @Integer
take_drop :: forall a. SymVal a => Proxy a -> IO Proof
take_drop p = runTP $
    lemma (atProxy p "take_drop")
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> take n xs ++ drop n xs .== xs)
          []

-- | @n .> 0 ==> take n (x .: xs) == x .: take (n - 1) xs@
--
-- >>> take_cons (Proxy @Integer)
-- Lemma: take_cons @Integer               Q.E.D.
-- [Proven] take_cons @Integer
take_cons :: forall a. SymVal a => Proxy a -> IO Proof
take_cons p = runTP $
   lemma (atProxy p "take_cons")
         (\(Forall @"n" n) (Forall @"x" x) (Forall @"xs" (xs :: SList a)) -> n .> 0 .=> take n (x .: xs) .== x .: take (n - 1) xs)
         []

-- | @take n (map f xs) == map f (take n xs)@
--
-- >>> take_map @Integer @Float (uninterpret "f")
-- Lemma: take_cons @Integer               Q.E.D.
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
take_map :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> IO Proof
take_map f = runTPWith z3{tpOptions = (tpOptions z3) {ribbonLength = 50}} $ do
    tc   <- use $ take_cons (Proxy @a)

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
-- >>> drop_cons (Proxy @Integer)
-- Lemma: drop_cons @Integer               Q.E.D.
-- [Proven] drop_cons @Integer
drop_cons :: forall a. SymVal a => Proxy a -> IO Proof
drop_cons p = runTP $
   lemma (atProxy p "drop_cons")
         (\(Forall @"n" n) (Forall @"x" x) (Forall @"xs" (xs :: SList a)) -> n .> 0 .=> drop n (x .: xs) .== drop (n - 1) xs)
         []

-- | @drop n (map f xs) == map f (drop n xs)@
--
-- >>> drop_map @Integer @String (uninterpret "f")
-- Lemma: drop_cons @Integer               Q.E.D.
-- Lemma: drop_cons @[Char]                Q.E.D.
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
drop_map :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> IO Proof
drop_map f = runTPWith z3{tpOptions = (tpOptions z3) {ribbonLength = 50}} $ do
   dcA <- use $ drop_cons (Proxy @a)
   dcB <- use $ drop_cons (Proxy @b)

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
-- >>> length_take (Proxy @Integer)
-- Lemma: length_take @Integer             Q.E.D.
-- [Proven] length_take @Integer
length_take :: forall a. SymVal a => Proxy a -> IO Proof
length_take p = runTP $
     lemma (atProxy p "length_take")
           (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> n .>= 0 .=> length (take n xs) .== length xs `smin` n)
           []

-- | @n >= 0 ==> length (drop n xs) == (length xs - n) \`max\` 0@
--
-- >>> length_drop (Proxy @Integer)
-- Lemma: length_drop @Integer             Q.E.D.
-- [Proven] length_drop @Integer
length_drop :: forall a. SymVal a => Proxy a -> IO Proof
length_drop p = runTP $
     lemma (atProxy p "length_drop")
           (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> n .>= 0 .=> length (drop n xs) .== (length xs - n) `smax` 0)
           []

-- | @length xs \<= n ==\> take n xs == xs@
--
-- >>> take_all (Proxy @Integer)
-- Lemma: take_all @Integer                Q.E.D.
-- [Proven] take_all @Integer
take_all :: forall a. SymVal a => Proxy a -> IO Proof
take_all p = runTP $
    lemma (atProxy p "take_all")
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> length xs .<= n .=> take n xs .== xs)
          []

-- | @length xs \<= n ==\> drop n xs == nil@
--
-- >>> drop_all (Proxy @Integer)
-- Lemma: drop_all @Integer                Q.E.D.
-- [Proven] drop_all @Integer
drop_all :: forall a. SymVal a => Proxy a -> IO Proof
drop_all p = runTP $
    lemma (atProxy p "drop_all")
          (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) -> length xs .<= n .=> drop n xs .== nil)
          []

-- | @take n (xs ++ ys) == (take n xs ++ take (n - length xs) ys)@
--
-- >>> take_append (Proxy @Integer)
-- Lemma: take_append @Integer             Q.E.D.
-- [Proven] take_append @Integer
take_append :: forall a. SymVal a => Proxy a -> IO Proof
take_append p = runTPWith cvc5 $
    lemma (atProxy p "take_append")
         (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> take n (xs ++ ys) .== take n xs ++ take (n - length xs) ys)
         []

-- | @drop n (xs ++ ys) == drop n xs ++ drop (n - length xs) ys@
--
-- NB. As of Feb 2025, z3 struggles to prove this, but cvc5 gets it out-of-the-box.
--
-- >>> drop_append (Proxy @Integer)
-- Lemma: drop_append @Integer             Q.E.D.
-- [Proven] drop_append @Integer
drop_append :: forall a. SymVal a => Proxy a -> IO Proof
drop_append p = runTP $
    lemmaWith cvc5 (atProxy p "drop_append")
                   (\(Forall @"n" n) (Forall @"xs" (xs :: SList a)) (Forall @"ys" ys) -> drop n (xs ++ ys) .== drop n xs ++ drop (n - length xs) ys)
                   []

-- * Zip

-- | @length xs == length ys ==> map fst (zip xs ys) = xs@
--
-- >>> map_fst_zip (Proxy @(Integer,Integer))
-- Inductive lemma: map_fst_zip @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_fst_zip @(Integer,Integer)
map_fst_zip :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> IO Proof
map_fst_zip p = runTP $
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
-- >>> map_snd_zip (Proxy @(Integer,Integer))
-- Inductive lemma: map_snd_zip @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_snd_zip @(Integer,Integer)
map_snd_zip :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> IO Proof
map_snd_zip p = runTP $
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
-- >>> map_fst_zip_take (Proxy @(Integer,Integer))
-- Lemma: take_cons @Integer               Q.E.D.
-- Inductive lemma: map_fst_zip_take @(Integer,Integer)
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] map_fst_zip_take @(Integer,Integer)
map_fst_zip_take :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> IO Proof
map_fst_zip_take p = runTP $ do
   tc <- use $ take_cons (Proxy @a)

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
-- >>> map_snd_zip_take (Proxy @(Integer,Integer))
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
map_snd_zip_take :: forall a b. (SymVal a, SymVal b) => Proxy (a, b) -> IO Proof
map_snd_zip_take p = runTP $ do
   tc <- use $ take_cons (Proxy @a)

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

-- * Counting

-- | Count the number of occurrences of an element in a list
count :: SymVal a => SBV a -> SList a -> SInteger
count = smtFunction "count" $ \e l -> ite (null l)
                                          0
                                          (let (x, xs) = uncons l
                                               cxs     = count e xs
                                           in ite (e .== x) (1 + cxs) cxs)

-- | @count e (xs ++ ys) == count e xs + count e ys@
--
-- >>> countAppend (Proxy @Integer)
-- Inductive lemma: countAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold count)                Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (simplify)                    Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countAppend @Integer
countAppend :: forall a. SymVal a => Proxy a -> IO Proof
countAppend p = runTP $
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
-- >>> takeDropCount (Proxy @Integer)
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
takeDropCount :: forall a. SymVal a => Proxy a -> IO Proof
takeDropCount p = runTP $ do
       capp     <- use $ countAppend p
       takeDrop <- use $ take_drop p

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
-- >>> countNonNegative (Proxy @Integer)
-- Inductive lemma: countNonNegative @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countNonNegative @Integer
countNonNegative :: forall a. SymVal a => Proxy a -> IO Proof
countNonNegative p = runTP $ do
   induct (atProxy p "countNonNegative")
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
-- >>> countElem (Proxy @Integer)
-- Inductive lemma: countNonNegative @Integer
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
countElem :: forall a. (Eq a, SymVal a) => Proxy a -> IO Proof
countElem p = runTP $ do

    cnn <- use $ countNonNegative p

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
-- >>> elemCount (Proxy @Integer)
-- Inductive lemma: elemCount @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] elemCount @Integer
elemCount :: forall a. (Eq a, SymVal a) => Proxy a -> IO Proof
elemCount p = runTP $
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
{- HLint ignore foldrMapFusion "Fuse foldr/map"    -}
{- HLint ignore filterConcat   "Move filter"       -}
{- HLint ignore module         "Use camelCase"     -}
{- HLint ignore module         "Use first"         -}
{- HLint ignore module         "Use second"        -}
{- HLint ignore module         "Use zipWith"       -}
