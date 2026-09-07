-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Lowering
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Structured results shared by the individual C lowering backends.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Lowering
  ( CLowering(..)
  , CRequirement(..)
  , CStorage(..)
  , expressionLowering
  , chooseLowering
  ) where

import Data.Maybe                     (catMaybes, listToMaybe)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ      (Doc)

-- | External facilities required by a lowered C fragment. The program-level
-- collector will ultimately turn these capabilities into includes, runtime
-- helpers, compiler options, and linker options.
data CRequirement = CRequiresGMP
                  | CRequiresLibBF
                  | CRequiresLibM
                  deriving (Eq, Ord, Show)

-- | Lifetime and ownership class of a lowered result.
data CStorage = CByValue         -- ^ An ordinary C value.
              | CFunctionScoped  -- ^ A reference valid until the generated function returns.
              | CCallerOwned     -- ^ Storage initialized and owned by the generated function's caller.
              deriving (Eq, Ord, Show)

-- | A C expression together with statements and capabilities needed around
-- its evaluation. Setup statements execute in list order; cleanup statements
-- execute in list order after the result has been consumed.
data CLowering = CLowering
  { loweringExpression   :: Doc                     -- ^ Expression producing the lowered result.
  , loweringSetup        :: [Doc]                   -- ^ Statements required before evaluation.
  , loweringCleanup      :: [Doc]                   -- ^ Statements required after consumption.
  , loweringRequirements :: Set.Set CRequirement    -- ^ Runtime and external capabilities used.
  , loweringStorage      :: CStorage                -- ^ Lifetime and ownership of the result.
  }

-- | Construct a statement-free expression lowering.
expressionLowering :: CStorage -> [CRequirement] -> Doc -> CLowering
expressionLowering storage requirements expression = CLowering
  { loweringExpression   = expression
  , loweringSetup        = []
  , loweringCleanup      = []
  , loweringRequirements = Set.fromList requirements
  , loweringStorage      = storage
  }

-- | Select the first backend that accepts an operation.
chooseLowering :: [Maybe CLowering] -> Maybe CLowering
chooseLowering = listToMaybe . catMaybes
