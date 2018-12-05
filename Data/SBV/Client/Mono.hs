-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Client.Mono
-- Copyright   :  (c) Brian Schroeder, Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Monomorphized versions of functions for simplified client use via
-- @Data.SBV@.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

module Data.SBV.Client.Mono where

import Data.SBV.Core.Data      (HasKind, Kind, Outputtable, Penalty, SymArray,
                                SymWord, SBool, SBV, SChar, SDouble, SFloat,
                                SInt8, SInt16, SInt32, SInt64, SInteger, SList,
                                SReal, SString, SW, SWord8, SWord16, SWord32,
                                SWord64)
import Data.SBV.Core.Model     (Metric)
import Data.SBV.Core.Symbolic  (Objective, Quantifier, Result, Symbolic,
                                SBVRunMode, SMTConfig, SVal)
import Data.SBV.Control.Types  (SMTOption)
import Data.SBV.Provers.Prover (Provable, SExecutable)

import qualified Data.SBV.Core.Data      as Trans
import qualified Data.SBV.Core.Model     as Trans
import qualified Data.SBV.Core.Symbolic  as Trans
import qualified Data.SBV.Provers.Prover as Trans

-- Data.SBV.Provers.Prover:

forAll_ :: Provable IO a => a -> Symbolic SBool
forAll_ = Trans.forAll_

forAll :: Provable IO a => [String] -> a -> Symbolic SBool
forAll = Trans.forAll

forSome_ :: Provable IO a => a -> Symbolic SBool
forSome_ = Trans.forSome_

forSome :: Provable IO a => [String] -> a -> Symbolic SBool
forSome = Trans.forSome

runSMT :: Symbolic a -> IO a
runSMT = Trans.runSMT

runSMTWith :: SMTConfig -> Symbolic a -> IO a
runSMTWith = Trans.runSMTWith

sName_ :: SExecutable IO a => a -> Symbolic ()
sName_ = Trans.sName_

sName :: SExecutable IO a => [String] -> a -> Symbolic ()
sName = Trans.sName

-- Data.SBV.Core.Data:

mkSymSBV :: Maybe Quantifier -> Kind -> Maybe String -> Symbolic (SBV a)
mkSymSBV = Trans.mkSymSBV

sbvToSymSW :: SBV a -> Symbolic SW
sbvToSymSW = Trans.sbvToSymSW

output :: Outputtable a => a -> Symbolic a
output = Trans.output

forall :: SymWord a => String -> Symbolic (SBV a)
forall = Trans.forall

forall_ :: SymWord a => Symbolic (SBV a)
forall_ = Trans.forall_

mkForallVars :: SymWord a => Int -> Symbolic [SBV a]
mkForallVars = Trans.mkForallVars

exists :: SymWord a => String -> Symbolic (SBV a)
exists = Trans.exists

exists_ :: SymWord a => Symbolic (SBV a)
exists_ = Trans.exists_

mkExistVars :: SymWord a => Int -> Symbolic [SBV a]
mkExistVars = Trans.mkExistVars

free :: SymWord a => String -> Symbolic (SBV a)
free = Trans.free

free_ :: SymWord a => Symbolic (SBV a)
free_ = Trans.free_

mkFreeVars :: SymWord a => Int -> Symbolic [SBV a]
mkFreeVars = Trans.mkFreeVars

symbolic :: SymWord a => String -> Symbolic (SBV a)
symbolic = Trans.symbolic

symbolics :: SymWord a => [String] -> Symbolic [SBV a]
symbolics = Trans.symbolics

mkSymWord :: SymWord a => Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
mkSymWord = Trans.mkSymWord

newArray_ :: (SymArray array, HasKind a, HasKind b) => Maybe (SBV b) -> Symbolic (array a b)
newArray_ = Trans.newArray_

newArray :: (SymArray array, HasKind a, HasKind b) => String -> Maybe (SBV b) -> Symbolic (array a b)
newArray = Trans.newArray

-- Data.SBV.Core.Model:

genVar :: Maybe Quantifier -> Kind -> String -> Symbolic (SBV a)
genVar = Trans.genVar

genVar_ :: Maybe Quantifier -> Kind -> Symbolic (SBV a)
genVar_ = Trans.genVar_

genMkSymVar :: Kind -> Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
genMkSymVar = Trans.genMkSymVar

sBool :: String -> Symbolic SBool
sBool = Trans.sBool

sBools :: [String] -> Symbolic [SBool]
sBools = Trans.sBools

sWord8 :: String -> Symbolic SWord8
sWord8 = Trans.sWord8

sWord8s :: [String] -> Symbolic [SWord8]
sWord8s = Trans.sWord8s

sWord16 :: String -> Symbolic SWord16
sWord16 = Trans.sWord16

sWord16s :: [String] -> Symbolic [SWord16]
sWord16s = Trans.sWord16s

sWord32 :: String -> Symbolic SWord32
sWord32 = Trans.sWord32

sWord32s :: [String] -> Symbolic [SWord32]
sWord32s = Trans.sWord32s

sWord64 :: String -> Symbolic SWord64
sWord64 = Trans.sWord64

sWord64s :: [String] -> Symbolic [SWord64]
sWord64s = Trans.sWord64s

sInt8 :: String -> Symbolic SInt8
sInt8 = Trans.sInt8

sInt8s :: [String] -> Symbolic [SInt8]
sInt8s = Trans.sInt8s

sInt16 :: String -> Symbolic SInt16
sInt16 = Trans.sInt16

sInt16s :: [String] -> Symbolic [SInt16]
sInt16s = Trans.sInt16s

sInt32 :: String -> Symbolic SInt32
sInt32 = Trans.sInt32

sInt32s :: [String] -> Symbolic [SInt32]
sInt32s = Trans.sInt32s

sInt64 :: String -> Symbolic SInt64
sInt64 = Trans.sInt64

sInt64s :: [String] -> Symbolic [SInt64]
sInt64s = Trans.sInt64s

sInteger :: String -> Symbolic SInteger
sInteger = Trans.sInteger

sIntegers :: [String] -> Symbolic [SInteger]
sIntegers = Trans.sIntegers

sReal :: String -> Symbolic SReal
sReal = Trans.sReal

sReals :: [String] -> Symbolic [SReal]
sReals = Trans.sReals

sFloat :: String -> Symbolic SFloat
sFloat = Trans.sFloat

sFloats :: [String] -> Symbolic [SFloat]
sFloats = Trans.sFloats

sDouble :: String -> Symbolic SDouble
sDouble = Trans.sDouble

sDoubles :: [String] -> Symbolic [SDouble]
sDoubles = Trans.sDoubles

sChar :: String -> Symbolic SChar
sChar = Trans.sChar

sString :: String -> Symbolic SString
sString = Trans.sString

sChars :: [String] -> Symbolic [SChar]
sChars = Trans.sChars

sStrings :: [String] -> Symbolic [SString]
sStrings = Trans.sStrings

sList :: (SymWord a) => String -> Symbolic (SList a)
sList = Trans.sList

sLists :: (SymWord a) => [String] -> Symbolic [SList a]
sLists = Trans.sLists

solve :: [SBool] -> Symbolic SBool
solve = Trans.solve

assertWithPenalty :: String -> SBool -> Penalty -> Symbolic ()
assertWithPenalty = Trans.assertWithPenalty

minimize :: Metric a => String -> a -> Symbolic ()
minimize = Trans.minimize

maximize :: Metric a => String -> a -> Symbolic ()
maximize = Trans.maximize

-- Data.SBV.Core.Symbolic:

svToSymSW :: SVal -> Symbolic SW
svToSymSW = Trans.svToSymSW

sWordN :: Int -> String -> Symbolic SVal
sWordN = Trans.sWordN

sWordN_ :: Int -> Symbolic SVal
sWordN_ = Trans.sWordN_

sIntN :: Int -> String -> Symbolic SVal
sIntN = Trans.sIntN

sIntN_ :: Int -> Symbolic SVal
sIntN_ = Trans.sIntN_

addAxiom :: String -> [String] -> Symbolic ()
addAxiom = Trans.addAxiom

runSymbolic :: SBVRunMode -> Symbolic a -> IO (a, Result)
runSymbolic = Trans.runSymbolic

addNewSMTOption :: SMTOption -> Symbolic ()
addNewSMTOption = Trans.addNewSMTOption

imposeConstraint :: Bool -> [(String, String)] -> SVal -> Symbolic ()
imposeConstraint = Trans.imposeConstraint

addSValOptGoal :: Objective SVal -> Symbolic ()
addSValOptGoal = Trans.addSValOptGoal

outputSVal :: SVal -> Symbolic ()
outputSVal = Trans.outputSVal
