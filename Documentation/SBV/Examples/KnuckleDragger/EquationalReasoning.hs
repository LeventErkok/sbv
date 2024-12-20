-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.EquationalReasoning
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various equalities that arise in functional-programming. A good source
-- is the classic book "Introduction to Functional Programming using Haskell,"
-- second edition. (Section 4.6 and others.)
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeAbstractions   #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.EquationalReasoning where

import Prelude hiding (concat, map, foldl, foldr, reverse, (<>), (++))

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

-- | Data declaration for an uninterpreted type, usually indicating source.
data A
mkUninterpretedSort ''A

-- | Data declaration for an uninterpreted type, usually indicating target.
data B
mkUninterpretedSort ''B

-- | Data declaration for an uninterpreted type, usually indicating an intermediate value.
data C
mkUninterpretedSort ''C

-- * Foldr-map fusion

-- | @foldr f a . map g = foldr (f . g) a@
--
-- We have:
--
-- >>> foldrMapFusion
-- Lemma: foldrMapFusion                   Q.E.D.
-- [Proven] foldrMapFusion
foldrMapFusion :: IO Proof
foldrMapFusion = runKD $ do
  let a :: SA
      a = uninterpret "a"

      g :: SC -> SB
      g = uninterpret "g"

      f :: SB -> SA -> SA
      f = uninterpret "f"

      p xs = foldr f a (map g xs) .== foldr (f . g) a xs

  lemma "foldrMapFusion" (\(Forall @"xs" xs) -> p xs) [induct p]

-- * Foldr-foldr fusion

-- |
--
-- @
--   Given f a = b and f (g x y) = h x (f y), for all x and y
--   We have: f . foldr g a = foldr h b
-- @
--
-- Note that, as of Dec 2024, z3 can't converge on this proof, but cvc5 gets it almost
-- instantaneously. We have:
--
-- >>> foldrFusion
-- Axiom: f a == b                         Axiom.
-- Axiom: f (g x) = h x (f y)              Axiom.
-- Lemma: foldrFusion                      Q.E.D.
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

       p xs = f (foldr g a xs) .== foldr h b xs

   -- f a == b
   h1 <- axiom "f a == b" $ f a .== b

   -- forall x, y: f (g x y) = h x (f y)
   h2 <- axiom "f (g x) = h x (f y)" $ \(Forall @"x" x) (Forall @"y" y) -> f (g x y) .== h x (f y)

   lemmaWith cvc5 "foldrFusion" (\(Forall @"xs" xs) -> p xs) [h1, h2, induct p]

-- * Foldr over append

-- | @foldr f a (xs ++ ys) == foldr f (foldr f a ys) xs@
--
-- We have:
--
-- >>> foldrOverAppend
-- Lemma: foldrOverAppend                  Q.E.D.
-- [Proven] foldrOverAppend
foldrOverAppend :: IO Proof
foldrOverAppend = runKD $ do
   let a :: SA
       a = uninterpret "a"

       f :: SA -> SA -> SA
       f = uninterpret "f"

       p xs ys = foldr f a (xs ++ ys) .== foldr f (foldr f a ys) xs

   lemma "foldrOverAppend"
          (\(Forall @"xs" xs) (Forall @"ys" ys) -> p xs ys)
          -- Induction is done on the last element. Here we want to induct on xs, hence the flip below.
          [induct (flip p)]

{- Can't converge
-- * Foldl over append

-- | @foldl f a (xs ++ ys) == foldl f (foldl f a xs) ys@
--
-- We have:
--
-- >>> foldlOverAppend
-- Lemma: foldrOverAppend                  Q.E.D.
-- [Proven] foldrOverAppend
foldlOverAppend :: IO Proof
foldlOverAppend = runKD $ do
   let f :: SA -> SA -> SA
       f = uninterpret "f"

       p a xs ys = foldl f a (xs ++ ys) .== foldl f (foldl f a xs) ys

   chainLemma "foldlOverAppend"
               (\(Forall @"a" a) (Forall @"xs" xs) (Forall @"ys" ys) -> p a xs ys)
               (\a x xs ys -> [ foldl f a ((x .: xs) ++ ys)
                              , foldl f a (x .: (xs ++ ys))
                              , foldl f (a `f` x) (xs ++ ys)
                              , foldl f (foldl f (a `f` x) xs) ys
                              ])
               -- Induction is done on the last element. Here we want to induct on xs, hence the rearrangement below
               [induct (flip . p)]
-}

{- can't converge
-- * Foldr-foldl correspondence

-- | @foldr f e xs == foldl (flip f) e (reverse xs)@
--
-- We have:
--
-- >> foldrFoldlReverse
foldrFoldlReverse :: IO Proof
foldrFoldlReverse = runKD $ do
   let e :: SB
       e = uninterpret "e"

       f :: SA -> SB -> SB
       f = uninterpret "f"

       p xs = foldr f e xs .== foldl (flip f) e (reverse xs)

   rc <- use $ runKD revCons

   chainLemma "foldrFoldlDuality"
              (\(Forall @"xs" xs) -> p xs)
              (\x xs -> [ -- foldr f e (x .: xs)
                        -- , x `f` foldr f e xs
                          foldl (flip f) e (reverse (x .: xs))
                        , foldl (flip f) e (reverse xs ++ singleton x)
                        , x `f` foldl (flip f) e (reverse xs)
                        ])
              [rc, induct p]
-}

{-
 --- Can't converge
-- * Bookkeeping law

-- | Provided @f@ is associative and @a@ is its right-unit: we have:
--
-- | @foldr f a . concat == foldr f a . map (foldr f a)@
--
-- We have:
--
-- >>> bookKeeping
bookKeeping :: IO Proof
bookKeeping = runKD $ do
   let a :: SA
       a = uninterpret "a"

       f :: SA -> SA -> SA
       f = uninterpret "f"

       p xss = foldr f a (concat xss) .== foldr f a (map (foldr f a) xss)

   assoc <- axiom "f is associative" (\(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x `f` (y `f` z) .== (x `f` y) `f` z)
   unit  <- axiom "a is right-unit"   (\(Forall @"x" x) -> x `f` a .== x)

   foa <- use foldrOverAppend

   chainLemma "bookKeeping"
              (\(Forall @"xss" xss) -> p xss)
              (\xs xss -> [ -- foldr f a (concat (xs .: xss))
                          -- , foldr f a (xs ++ concat xss)
                          -- , foldr f (foldr f a (concat xss)) xs
                          -- , foldr f (foldr f a (map (foldr f a) xss)) xs

                            f (foldr f a xs) (foldr f a (map (foldr f a) xss))
                          , foldr f (foldr f a (map (foldr f a) xss)) (singleton (foldr f a xs))
                          , foldr f a (singleton (foldr f a xs) ++ map (foldr f a) xss)
                          , foldr f a (foldr f a xs .: map (foldr f a) xss)
                          , foldr f a (map (foldr f a) (xs .: xss))
                          ])
              [assoc, unit, foa, induct p]
-}

{----------------
-- TODO: Can't converge on this either..
-- | First duality theorem. Given:
--
-- @
--     x @ (y @ z) = (x @ y) @ z     (associativity of @)
-- and e @ x = x                     (left unit)
-- and x @ e = x                     (right unit)
-- @
--
-- Prove:
--
-- @
--     foldr (@) e xs = foldl (@) e xs
-- @
--
-- We have:
--
-- >>> firstDuality
firstDuality :: IO Proof
firstDuality  = runKD $ do
   let (@) :: SA -> SA -> SA
       (@) = uninterpret "|@|"

       e :: SA
       e = uninterpret "e"

   axm1 <- axiom "@ is associative" (\(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x @ (y @ z) .== (x @ y) @ z)
   axm2 <- axiom "e is left unit"   (\(Forall @"x" x) -> e @ x .== x)
   axm3 <- axiom "e is right unit"  (\(Forall @"x" x) -> x @ e .== x)

   let p xs = foldr (@) e xs .== foldl (@) e xs

   -- Helper: foldl (@) (y @ z) xs = y @ foldl (@) z xs
   h <- do
      let hp y z xs = foldl (@) (y @ z) xs .== y @ foldl (@) z xs

      chainLemma "foldl over @"
                 (\(Forall @"y" y) (Forall @"z" z) (Forall @"xs" xs) -> hp y z xs)
                 (\y z x xs -> [ foldl (@) (y @ z) (x .: xs)
                               , foldl (@) ((y @ z) @ x) xs
                               , foldl (@) (y @ (z @ x)) xs
                               -- this transition is hard
                               , y @ foldl (@) (z @ x) xs
                               , y @ foldl (@) z (x .: xs)
                               ])
                 [axm1, axm2, induct hp]

   lemma "firstDuality" (\(Forall @"xs" xs) -> p xs) [axm1, axm2, axm3, h, induct p]
-}

{- TODO: Can't converge on this one. The strengthened induction axiom requires a very careful
   instantiation of the inductive hypothesis, which I can't get through. Perhaps we need proper
   support for patterns.

-- | Given:
-- @
--        (x <> y) @ z = x \<> (y \@ z)
--   and  e \@ x = x \<> e
-- @
--
-- Proves:
--
-- @
--    foldl (\@\) e xs = foldr (\<>) e xs@
-- @
--
-- We have:
--
-- >>> foldrFoldl
foldrFoldl :: IO Proof
foldrFoldl = runKD $ do

   let -- Declare the operators as uninterpreted functions
       (@) :: SB -> SA -> SB
       (@) = uninterpret "|@|"

       (<>) :: SA -> SB -> SB
       (<>) = uninterpret "|<>|"

       -- The unit element
       e :: SB
       e = uninterpret "e"

       -- Equivalence predicate
       p :: SList A -> SBool
       p xs = foldl (@) e xs .== foldr (<>) e xs


   -- Assumptions about the operators

   -- (x <> y) @ z == x <> (y @ z)
   axm1 <- axiom "<> over @" $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z)
                                  -> (x <> y) @ z .== x <> (y @ z)

   -- e @ x == x <> e
   axm2 <- axiom "unit" $ \(Forall @"x" x) -> e @ x .== x <> e

   -- Helper: foldl (@) (y <> z) xs = y <> foldl (@) z xs
   h <- do
      let hp y z xs = foldl (@) (y <> z) xs .== y <> foldl (@) z xs

      chainLemma "foldl over @"
                 (\(Forall @"y" y) (Forall @"z" z) (Forall @"xs" xs) -> hp y z xs)
                 (\y z x xs -> [ foldl (@) (y <> z) (x .: xs)
                               , foldl (@) ((y <> z) @ x) xs
                               , foldl (@) (y <> (z @ x)) xs
                               -- this transition is hard
                               , y <> foldl (@) (z @ x) xs
                               , y <> foldl (@) z (x .: xs)
                               ])
                 [axm1, axm2, induct hp]

   -- Final proof:
   lemma "foldrFoldl" (\(Forall @"xs" xs) -> p xs) [axm1, axm2, h, induct p]
-}
