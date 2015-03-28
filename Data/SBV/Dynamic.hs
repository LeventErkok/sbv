---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Dynamic
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Dynamically typed low-level API to the SBV library, for users who
-- want to generate symbolic values at run-time. Note that with this
-- API it is possible to create terms that are not type correct; use
-- at your own risk!
---------------------------------------------------------------------------------

module Data.SBV.Dynamic
  ( Kind(..)
  , Symbolic
  , Quantifier(..)
  , SVal
  , svKind
  , svBitSize, svSigned
  , svMkSymVar
  -- ** Basic constructors
  , svTrue, svFalse, svBool
  , svInteger
  , svAsBool
  -- ** Basic operations
  , svPlus, svTimes, svMinus, svUNeg, svAbs
  , svDivide, svQuot, svRem
  , svEqual, svNotEqual
  , svLessThan, svGreaterThan, svLessEq, svGreaterEq
  , svAnd, svOr, svXOr, svNot
  , svShl, svShr, svRol, svRor
  , svExtract, svJoin
  , svUninterpreted
  , svIte, svLazyIte, svSymbolicMerge
  , svSelect
  -- ** Derived operations
  , svToWord1, svFromWord1, svTestBit
  , svShiftLeft, svShiftRight
  , svRotateLeft, svRotateRight
  ) where

import Data.SBV.BitVectors.Kind
import Data.SBV.BitVectors.Symbolic
import Data.SBV.BitVectors.Operations
