-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.FoldrLaws
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various fold related laws, inspired by Section 4.6 of Richard Bird's
-- classic book "Introduction to Functional Programming using Haskell,"
-- second edition.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeAbstractions   #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.FoldLaws where

import Prelude hiding (foldl, foldr, (<>))

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

-- | Data declaration for an uninterpreted source type.
data A
mkUninterpretedSort ''A

-- | Data declaration for an uninterpreted target type.
data B
mkUninterpretedSort ''B

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

----------------------------------------------------------------------------------------
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
