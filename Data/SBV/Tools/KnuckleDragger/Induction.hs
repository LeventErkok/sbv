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

{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger.Induction (
      inductionPrinciple
    ) where


import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | Given a predicate, return an induction principle for it.
class Induction a where
  inductionPrinciple :: (a -> SBool) -> IO Proven

-- | Induction over naturals. Note that the parameter here is over 'SInteger', which is a superset
-- of naturals. The principle returned will be able to establish proofs of the form n >= 0 .=> P n.
instance Induction SInteger where
   inductionPrinciple p = do
    let qb = quantifiedBool

        principle =       p 0 .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                  .=> qb -----------------------------------------------------------
                                    (\(Forall n) -> n .>= 0 .=> p n)

    axiom "Nat.induction" principle
