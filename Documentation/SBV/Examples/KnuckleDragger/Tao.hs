-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Tao
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves a problem originating in algebra:
--   https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity/
--
-- Apparently this was posed by Terrence Tao: https://mathstodon.xyz/@tao/110736805384878353
--
-- Essentially, for an arbitrary binary operation op, we prove that
--
-- @
--    (x op x) op y == y op x
-- @
--
-- Implies that @op@ must be commutative.
-----------------------------------------------------------------------------


{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitForAll     #-}
{-# LANGUAGE TypeAbstractions   #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Tao where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> :set -XTypeApplications
#endif

-- | Create an uninterpreted type to do the proofs over.
data T
mkUninterpretedSort ''T

-- | Prove that:
--
--  @
--    (x op x) op y == y op x
--  @
--
--  means that @op@ is commutative.
--
-- We have:
--
-- >>> tao @T (uninterpret "op")
-- Lemma: tao                              Q.E.D.
-- [Proven] tao
tao :: forall a. SymVal a => (SBV a -> SBV a -> SBV a) -> IO Proof
tao op = runKD $
   lemma "tao" (    quantifiedBool (\(Forall @"x" x) (Forall @"y" y) -> ((x `op` x) `op` y) .== y `op` x)
                .=> quantifiedBool (\(Forall @"x" x) (Forall @"y" y) -> (x `op` y) .== (y `op` x)))
               []
