-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Float
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of arbitrary float operations.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Float (
        -- * Type-sized floats
        FP(..)

        -- * Constructing values
        , fpFromRawRep, fpFromBigFloat, fpNaN, fpInf, fpZero

        -- * Operations
        , fpFromInteger, fpFromRational, fpFromFloat, fpFromDouble, fpEncodeFloat
        ) where

import Data.SBV.Core.SizedFloats
