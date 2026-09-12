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
  , expressionLowering
  , chooseLowering
  ) where

import Data.Maybe                     (catMaybes, listToMaybe)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ      (Doc)

-- | Facilities required by a lowered C fragment. The program-level
-- collector will ultimately turn these capabilities into includes, runtime
-- helpers, compiler options, and linker options.
data CRequirement = CRequiresGMP              -- ^ GMP-backed exact-number support.
                  | CRequiresLibBF            -- ^ LibBF-backed arbitrary floating-point support.
                  | CRequiresLibM             -- ^ The platform C mathematics library.
                  | CRequiresNativeFPRounding -- ^ LibBF adapters for explicitly rounded native floating-point operations.
                  | CRequiresWideBV           -- ^ Exact-width limb-backed bit-vector support.
                  | CRequiresArrays           -- ^ Persistent functional-array support.
                  | CRequiresText             -- ^ Length-aware character and string support.
                  | CRequiresLists            -- ^ Typed symbolic-list support.
                  | CRequiresSets             -- ^ Finite/cofinite symbolic-set support.
                  | CRequiresFunctionResults  -- ^ Stable private storage for owned aggregate function results.
                  | CRequiresIntegerPower     -- ^ Modular exponentiation for mapped unbounded integers.
                  deriving (Eq, Ord, Show)

-- | A C expression together with statements and capabilities needed around
-- its evaluation. Declarations may be hoisted for function-wide backing
-- storage, but setup statements execute in order only when the value is demanded.
data CLowering = CLowering
  { loweringExpression   :: Doc                     -- ^ Expression producing the lowered result.
  , loweringDeclarations :: [Doc]                   -- ^ Declarations that may be hoisted above guarded control flow.
  , loweringSetup        :: [Doc]                   -- ^ Statements required before evaluation.
  , loweringRequirements :: Set.Set CRequirement    -- ^ Runtime and external capabilities used.
  }

-- | Construct a statement-free expression lowering.
expressionLowering :: [CRequirement] -> Doc -> CLowering
expressionLowering requirements expression = CLowering
  { loweringExpression   = expression
  , loweringDeclarations = []
  , loweringSetup        = []
  , loweringRequirements = Set.fromList requirements
  }

-- | Select the first backend that accepts an operation.
chooseLowering :: [Maybe CLowering] -> Maybe CLowering
chooseLowering = listToMaybe . catMaybes
