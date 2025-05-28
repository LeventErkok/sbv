-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Tao
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A question posed by Terrence Tao: <https://mathstodon.xyz/@tao/110736805384878353>.
-- Essentially, for an arbitrary binary operation op, we prove that
--
-- @
--    (x op x) op y == y op x
-- @
--
-- Implies @op@ must be commutative.
-----------------------------------------------------------------------------


{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Tao where

import Data.SBV
import Data.SBV.Tools.TP

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
tao op = runTP $
   lemma "tao" (    quantifiedBool (\(Forall @"x" x) (Forall @"y" y) -> ((x `op` x) `op` y) .== y `op` x)
                .=> quantifiedBool (\(Forall @"x" x) (Forall @"y" y) -> (x `op` y) .== (y `op` x)))
               []
