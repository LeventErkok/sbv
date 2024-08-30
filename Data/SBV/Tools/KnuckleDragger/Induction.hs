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

-- | Given a predicate on integers, return an induction principle which would prove it for all n >= 0.
inductionPrinciple :: String -> (SInteger -> SBool) -> IO (SInteger -> SBool, Proven)
inductionPrinciple nm p = do
    let qb = quantifiedBool

        principle =       p 0 .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                  .=> qb -----------------------------------------------------------
                                    (\(Forall n) -> n .>= 0 .=> p n)

    induction <- axiom (nm ++ "_induction") principle

    pure (p, induction)
