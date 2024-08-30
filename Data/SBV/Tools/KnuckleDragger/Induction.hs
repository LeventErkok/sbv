-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KnuckleDragger.Induction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Induction axiom for KnuckleDragger
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger.Induction (
      Induction(..)
    ) where

import Data.SBV
import qualified Data.SBV.List as SL

import Data.SBV.Tools.KnuckleDragger

-- | Given a predicate, return an induction principle for it. Typically, we only have one viable
-- induction principle for a given type, but we allow for alternative ones.
class Induction a where
  inductionPrinciple  :: (a -> SBool) -> IO Proven
  inductionPrinciple2 :: (a -> SBool) -> IO Proven
  inductionPrinciple3 :: (a -> SBool) -> IO Proven

  -- The second and third principles are the same as first by default, unless we provide them
  -- explicitly.
  inductionPrinciple2 = inductionPrinciple
  inductionPrinciple3 = inductionPrinciple

-- | Induction over SInteger. We provide various induction principles here: The first one
-- is over naturals, will only prove predicates that explicitly restrict the argument to >= 0.
-- The second and third ones are induction over the entire range of integers, two different
-- principles that might work better for different problems.
instance Induction SInteger where

   -- | Induction over naturals. Will prove predicates of the form @\n -> n >= 0 .=> predicate n@.
   inductionPrinciple p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                    .=> qb -----------------------------------------------------------
                                      (\(Forall n) -> n .>= 0 .=> p n)

      axiom "Nat.induction" principle

   -- | Induction over integers, using the strategy that @P(n)@ is equivalent to @P(n+1)@
   -- (i.e., not just @P(n) => P(n+1)@), thus covering the entire range.
   inductionPrinciple2 p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall i) -> p i .== p (i+1))
                    .=> qb ---------------------------------------------
                                    (\(Forall i) -> p i)

      axiom "Integer.induction" principle

   -- | Induction over integers, using the strategy that @P(n) => P(n+1)@ and @P(n) => P(n-1)@.
   inductionPrinciple3 p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall i) -> p i .=> p (i+1) .&& p (i-1))
                    .=> qb ---------------------------------------------------------
                                           (\(Forall i) -> p i)

      axiom "Integer.splitInduction" principle

-- | Induction over lists
instance SymVal a => Induction (SList a) where
  inductionPrinciple p = do
     let qb a = quantifiedBool a

         principle =       p SL.nil .&& qb (\(Forall x) (Forall xs) -> p xs .=> p (x SL..: xs))
                   .=> qb ----------------------------------------------------------------------
                                             (\(Forall xs) -> p xs)

     axiom "List(a).induction" principle
