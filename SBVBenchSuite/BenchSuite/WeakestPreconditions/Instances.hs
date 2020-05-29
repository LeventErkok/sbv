-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.Instance
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Helper file to provide common orphaned instances for WeakestPrecondition benchmarks
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.WeakestPreconditions.Instances where

import Data.SBV.Tools.WeakestPreconditions

import Control.DeepSeq


-- | orphaned instance for benchmarks
instance NFData a => NFData (ProofResult a) where rnf x = seq x ()
instance NFData a => NFData (Status a) where rnf x = seq x ()
