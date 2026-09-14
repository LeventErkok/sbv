-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Default SBV-to-C compiler. This module deliberately remains a thin facade
-- so the implementation can coexist with the compatibility backend in
-- "Data.SBV.Compilers.C.Legacy".
--
-- == Execution model and supported values
--
-- The compiler evaluates a finite symbolic expression graph; it does not
-- invoke an SMT solver at run time. Generated standalone programs and static
-- libraries support:
--
-- * Booleans and signed or unsigned bit-vectors of any positive width.
-- * Exact GMP-backed integers, rational-valued reals, and rationals. The
--   historical bounded integer and native floating-point real mappings remain
--   available through @cgIntegerSize@ and @cgSRealType@.
-- * Native and arbitrary-format IEEE floating point. Arbitrary formats and
--   directed native rounding use LibBF.
-- * Characters, strings, lists, finite or cofinite sets, tuples, and concrete
--   algebraic datatypes, including recursive datatypes.
-- * Finite lookup tables and persistent arrays created from constants,
--   writes, retained lambdas, or caller-provided lookup callbacks. Direct
--   array equality enumerates supported finite key domains, subject to
--   @cgArrayEqualityLimit@ (256 keys by default).
-- * First-order @smtFunction@ definitions and SBV's firstified
--   @smtHOFunction@ specializations, including recursive and mutually
--   recursive groups, closed nested array lambdas, explicit closure
--   environments, hard constraints as executable preconditions, scalar and
--   grouped results, and multi-function static libraries.
-- * Regular-expression membership and language equality, compiled using bounded
--   automata without additional dependencies. Generation budgets are configurable;
--   successfully generated matchers accept strings of arbitrary length.
--
-- Numeric lowering includes exact-width arithmetic, comparisons, shifts,
-- rotations, joins and extractions, overflow predicates, conversions,
-- divisibility, and integer exponentiation. Mapped reals additionally support
-- the C @libm@ transcendental operations. Exact rational reals reject those
-- operations because their results cannot in general be represented by GMP
-- rationals; select @cgSRealType@ when an approximation is acceptable.
--
-- == Deliberate boundaries
--
-- Quantifiers, special solver relations, uninterpreted sorts, and soft
-- constraints are rejected. General extensional array equality and arrays nested
-- in compared values remain unsupported. Array lambdas must be closed; capturing
-- outer symbolic values is rejected during generation. The C backend compiles
-- higher-order uses after SBV has firstified them; it does not expose symbolic
-- functions as runtime C values.
--
-- Import "Data.SBV.Compilers.C.Legacy" to retain the previous compiler while
-- migrating code that encounters one of these boundaries.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C
  ( compileToC
  , compileToCLib
  , compileToC'
  , compileToCLib'
  ) where

import Data.SBV.Compilers.C.New (compileToC, compileToC', compileToCLib, compileToCLib')
