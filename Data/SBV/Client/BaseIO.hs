-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Client.BaseIO
-- Copyright : (c) Brian Schroeder
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Monomorphized versions of functions for simplified client use via
-- @Data.SBV@, where we restrict the underlying monad to be IO.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Client.BaseIO where

import Data.SBV.Core.Data      (HasKind, Kind, Outputtable, Penalty, SymArray,
                                SymVal, SBool, SBV, SChar, SDouble, SFloat,
                                SFPHalf, SFPBFloat, SFPSingle, SFPDouble, SFPQuad, SFloatingPoint,
                                SInt8, SInt16, SInt32, SInt64, SInteger, SList,
                                SReal, SString, SV, SWord8, SWord16, SWord32,
                                SWord64, SEither, SRational, SMaybe, SSet, constrain, (.==))
import Data.SBV.Core.Sized     (SInt, SWord, IntN, WordN)
import Data.SBV.Core.Kind      (BVIsNonZero, ValidFloat)
import Data.SBV.Core.Model     (Metric(..), SymTuple)
import Data.SBV.Core.Symbolic  (Objective, OptimizeStyle, Result, VarContext, Symbolic, SBVRunMode, SMTConfig,
                                SVal, symbolicEnv, rPartitionVars, State(..))
import Data.SBV.Control.Types  (SMTOption)
import Data.SBV.Provers.Prover (Provable, Satisfiable, SExecutable, ThmResult)
import Data.SBV.SMT.SMT        (AllSatResult, SafeResult, SatResult,
                                OptimizeResult)

import GHC.TypeLits (KnownNat, TypeError, ErrorMessage(..))
import Data.Kind

import Data.Int
import Data.Word

import Data.IORef(readIORef, writeIORef)

import qualified Data.SBV.Core.Data      as Trans
import qualified Data.SBV.Core.Sized     as Trans
import qualified Data.SBV.Core.Model     as Trans
import qualified Data.SBV.Core.Symbolic  as Trans
import qualified Data.SBV.Provers.Prover as Trans

import Control.Monad.Trans (liftIO)

-- | Prove a predicate, using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.prove'
prove :: Provable a => a -> IO ThmResult
prove = Trans.prove

-- | Prove the predicate using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.proveWith'
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith = Trans.proveWith

-- | Prove a predicate with delta-satisfiability, using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.prove'
dprove :: Provable a => a -> IO ThmResult
dprove = Trans.dprove

-- | Prove the predicate with delta-satisfiability using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.proveWith'
dproveWith :: Provable a => SMTConfig -> a -> IO ThmResult
dproveWith = Trans.dproveWith

-- | Find a satisfying assignment for a predicate, using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sat'
sat :: Satisfiable a => a -> IO SatResult
sat = Trans.sat

-- | Find a satisfying assignment using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.satWith'
satWith :: Satisfiable a => SMTConfig -> a -> IO SatResult
satWith = Trans.satWith

-- | Find a delta-satisfying assignment for a predicate, using the default solver for delta-satisfiability.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.dsat'
dsat :: Satisfiable a => a -> IO SatResult
dsat = Trans.dsat

-- | Find a satisfying assignment using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.satWith'
dsatWith :: Satisfiable a => SMTConfig -> a -> IO SatResult
dsatWith = Trans.dsatWith

-- | Find all satisfying assignments, using the default solver.
-- Equivalent to @'allSatWith' 'Data.SBV.defaultSMTCfg'@. See 'allSatWith' for details.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.allSat'
allSat :: Satisfiable a => a -> IO AllSatResult
allSat = Trans.allSat

-- | Return all satisfying assignments for a predicate.
-- Note that this call will block until all satisfying assignments are found. If you have a problem
-- with infinitely many satisfying models (consider 'SInteger') or a very large number of them, you
-- might have to wait for a long time. To avoid such cases, use the 'Data.SBV.Core.Symbolic.allSatMaxModelCount'
-- parameter in the configuration.
--
-- NB. Uninterpreted constant/function values and counter-examples for array values are ignored for
-- the purposes of 'allSat'. That is, only the satisfying assignments modulo uninterpreted functions and
-- array inputs will be returned. This is due to the limitation of not having a robust means of getting a
-- function counter-example back from the SMT solver.
--  Find all satisfying assignments using the given SMT-solver
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.allSatWith'
allSatWith :: Satisfiable a => SMTConfig -> a -> IO AllSatResult
allSatWith = Trans.allSatWith

-- | Optimize a given collection of `Objective`s.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.optimize'
optimize :: Satisfiable a => OptimizeStyle -> a -> IO OptimizeResult
optimize = Trans.optimize

-- | Optimizes the objectives using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.optimizeWith'
optimizeWith :: Satisfiable a => SMTConfig -> OptimizeStyle -> a -> IO OptimizeResult
optimizeWith = Trans.optimizeWith

-- | Check if the constraints given are consistent in a prove call using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isVacuousProof'
isVacuousProof :: Provable a => a -> IO Bool
isVacuousProof = Trans.isVacuousProof

-- | Determine if the constraints are vacuous in a SAT call using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isVacuousProofWith'
isVacuousProofWith :: Provable a => SMTConfig -> a -> IO Bool
isVacuousProofWith = Trans.isVacuousProofWith

-- | Checks theoremhood using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isTheorem'
isTheorem :: Provable a => a -> IO Bool
isTheorem = Trans.isTheorem

-- | Check whether a given property is a theorem.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isTheoremWith'
isTheoremWith :: Provable a => SMTConfig -> a -> IO Bool
isTheoremWith = Trans.isTheoremWith

-- | Checks satisfiability using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isSatisfiable'
isSatisfiable :: Satisfiable a => a -> IO Bool
isSatisfiable = Trans.isSatisfiable

-- | Check whether a given property is satisfiable.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isSatisfiableWith'
isSatisfiableWith :: Satisfiable a => SMTConfig -> a -> IO Bool
isSatisfiableWith = Trans.isSatisfiableWith

-- | Run an arbitrary symbolic computation, equivalent to @'runSMTWith' 'Data.SBV.defaultSMTCfg'@
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.runSMT'
runSMT :: Symbolic a -> IO a
runSMT = Trans.runSMT

-- | Runs an arbitrary symbolic computation, exposed to the user in SAT mode
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.runSMTWith'
runSMTWith :: SMTConfig -> Symbolic a -> IO a
runSMTWith = Trans.runSMTWith

-- | Create an argument for a name used in a safety-checking call.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sName_'
sName :: SExecutable IO a => a -> Symbolic ()
sName = Trans.sName

-- | Check safety using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.safe'
safe :: SExecutable IO a => a -> IO [SafeResult]
safe = Trans.safe

-- | Check if any of the 'Data.SBV.sAssert' calls can be violated.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.safeWith'
safeWith :: SExecutable IO a => SMTConfig -> a -> IO [SafeResult]
safeWith = Trans.safeWith

-- Data.SBV.Core.Data:

-- | Create a symbolic variable.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkSymSBV'
mkSymSBV :: VarContext -> Kind -> Maybe String -> Symbolic (SBV a)
mkSymSBV = Trans.mkSymSBV

-- | Convert a symbolic value to an SV, inside the Symbolic monad
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sbvToSymSV'
sbvToSymSV :: SBV a -> Symbolic SV
sbvToSymSV = Trans.sbvToSymSV

-- | Mark an interim result as an output. Useful when constructing Symbolic programs
-- that return multiple values, or when the result is programmatically computed.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.output'
output :: Outputtable a => a -> Symbolic a
output = Trans.output

-- | Create a partitioning constraint, for all-sat calls.
partition :: SymVal a => String -> SBV a -> Symbolic ()
partition nm term = do
   State{rPartitionVars} <- symbolicEnv

   -- Generate a unique variable with the prefix nm if necessary and
   -- add it to partitions
   fresh <- liftIO $ do olds <- readIORef rPartitionVars
                        let new = case filter (`notElem` olds) (nm : [nm ++ "_" ++ show i | i <- [(1 :: Int) ..]]) of
                                    h:_ -> h
                                    []  -> error $ "Impossible: Can't get a fresh variable from infinite list in partition." ++ show (nm, term)
                        writeIORef rPartitionVars (olds ++ [new])
                        pure new

   -- declare and constrain
   v <- free fresh
   constrain $ v .== term

-- | Create a free variable, universal in a proof, existential in sat
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.free'
free :: SymVal a => String -> Symbolic (SBV a)
free = Trans.free

-- | Create an unnamed free variable, universal in proof, existential in sat
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.free_'
free_ :: SymVal a => Symbolic (SBV a)
free_ = Trans.free_

-- | Create a bunch of free vars
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkFreeVars'
mkFreeVars :: SymVal a => Int -> Symbolic [SBV a]
mkFreeVars = Trans.mkFreeVars

-- | Similar to free; Just a more convenient name
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.symbolic'
symbolic :: SymVal a => String -> Symbolic (SBV a)
symbolic = Trans.symbolic

-- | Similar to mkFreeVars; but automatically gives names based on the strings
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.symbolics'
symbolics :: SymVal a => [String] -> Symbolic [SBV a]
symbolics = Trans.symbolics

-- | One stop allocator
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkSymVal'
mkSymVal :: SymVal a => VarContext -> Maybe String -> Symbolic (SBV a)
mkSymVal = Trans.mkSymVal

-- | Create a new anonymous array, possibly with a default initial value.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.newArray_'
newArray_ :: (SymArray array, HasKind a, HasKind b) => Maybe (SBV b) -> Symbolic (array a b)
newArray_ = Trans.newArray_

-- | Create a named new array, possibly with a default initial value.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.newArray'
newArray :: (SymArray array, HasKind a, HasKind b) => String -> Maybe (SBV b) -> Symbolic (array a b)
newArray = Trans.newArray

-- Data.SBV.Core.Model:

-- | Generically make a symbolic var
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.genMkSymVar'
genMkSymVar :: Kind -> VarContext -> Maybe String -> Symbolic (SBV a)
genMkSymVar = Trans.genMkSymVar

-- | Declare a named 'SBool'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sBool'
sBool :: String -> Symbolic SBool
sBool = Trans.sBool

-- | Declare an unnamed 'SBool'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sBool_'
sBool_ :: Symbolic SBool
sBool_ = Trans.sBool_

-- | Declare a list of 'SBool's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sBools'
sBools :: [String] -> Symbolic [SBool]
sBools = Trans.sBools

-- | Declare a named 'SWord8'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord8'
sWord8 :: String -> Symbolic SWord8
sWord8 = Trans.sWord8

-- | Declare an unnamed 'SWord8'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord8_'
sWord8_ :: Symbolic SWord8
sWord8_ = Trans.sWord8_

-- | Declare a list of 'SWord8's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord8s'
sWord8s :: [String] -> Symbolic [SWord8]
sWord8s = Trans.sWord8s

-- | Declare a named 'SWord16'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord16'
sWord16 :: String -> Symbolic SWord16
sWord16 = Trans.sWord16

-- | Declare an unnamed 'SWord16'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord16_'
sWord16_ :: Symbolic SWord16
sWord16_ = Trans.sWord16_

-- | Declare a list of 'SWord16's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord16s'
sWord16s :: [String] -> Symbolic [SWord16]
sWord16s = Trans.sWord16s

-- | Declare a named 'SWord32'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord32'
sWord32 :: String -> Symbolic SWord32
sWord32 = Trans.sWord32

-- | Declare an unnamed 'SWord32'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord32_'
sWord32_ :: Symbolic SWord32
sWord32_ = Trans.sWord32_

-- | Declare a list of 'SWord32's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord32s'
sWord32s :: [String] -> Symbolic [SWord32]
sWord32s = Trans.sWord32s

-- | Declare a named 'SWord64'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord64'
sWord64 :: String -> Symbolic SWord64
sWord64 = Trans.sWord64

-- | Declare an unnamed 'SWord64'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord64_'
sWord64_ :: Symbolic SWord64
sWord64_ = Trans.sWord64_

-- | Declare a list of 'SWord64's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord64s'
sWord64s :: [String] -> Symbolic [SWord64]
sWord64s = Trans.sWord64s

-- | Declare a named 'SWord'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord'
sWord :: (KnownNat n, BVIsNonZero n) => String -> Symbolic (SWord n)
sWord = Trans.sWord

-- | Declare an unnamed 'SWord'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord_'
sWord_ :: (KnownNat n, BVIsNonZero n) => Symbolic (SWord n)
sWord_ = Trans.sWord_

-- | Declare a list of 'SWord8's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWords'
sWords :: (KnownNat n, BVIsNonZero n) => [String] -> Symbolic [SWord n]
sWords = Trans.sWords

-- | Declare a named 'SInt8'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt8'
sInt8 :: String -> Symbolic SInt8
sInt8 = Trans.sInt8

-- | Declare an unnamed 'SInt8'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt8_'
sInt8_ :: Symbolic SInt8
sInt8_ = Trans.sInt8_

-- | Declare a list of 'SInt8's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt8s'
sInt8s :: [String] -> Symbolic [SInt8]
sInt8s = Trans.sInt8s

-- | Declare a named 'SInt16'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt16'
sInt16 :: String -> Symbolic SInt16
sInt16 = Trans.sInt16

-- | Declare an unnamed 'SInt16'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt16_'
sInt16_ :: Symbolic SInt16
sInt16_ = Trans.sInt16_

-- | Declare a list of 'SInt16's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt16s'
sInt16s :: [String] -> Symbolic [SInt16]
sInt16s = Trans.sInt16s

-- | Declare a named 'SInt32'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt32'
sInt32 :: String -> Symbolic SInt32
sInt32 = Trans.sInt32

-- | Declare an unnamed 'SInt32'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt32_'
sInt32_ :: Symbolic SInt32
sInt32_ = Trans.sInt32_

-- | Declare a list of 'SInt32's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt32s'
sInt32s :: [String] -> Symbolic [SInt32]
sInt32s = Trans.sInt32s

-- | Declare a named 'SInt64'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt64'
sInt64 :: String -> Symbolic SInt64
sInt64 = Trans.sInt64

-- | Declare an unnamed 'SInt64'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt64_'
sInt64_ :: Symbolic SInt64
sInt64_ = Trans.sInt64_

-- | Declare a list of 'SInt64's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt64s'
sInt64s :: [String] -> Symbolic [SInt64]
sInt64s = Trans.sInt64s

-- | Declare a named 'SInt'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt'
sInt :: (KnownNat n, BVIsNonZero n) => String -> Symbolic (SInt n)
sInt = Trans.sInt

-- | Declare an unnamed 'SInt'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt_'
sInt_ :: (KnownNat n, BVIsNonZero n) => Symbolic (SInt n)
sInt_ = Trans.sInt_

-- | Declare a list of 'SInt's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInts'
sInts :: (KnownNat n, BVIsNonZero n) => [String] -> Symbolic [SInt n]
sInts = Trans.sInts

-- | Declare a named 'SInteger'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInteger'
sInteger :: String -> Symbolic SInteger
sInteger = Trans.sInteger

-- | Declare an unnamed 'SInteger'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInteger_'
sInteger_ :: Symbolic SInteger
sInteger_ = Trans.sInteger_

-- | Declare a list of 'SInteger's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sIntegers'
sIntegers :: [String] -> Symbolic [SInteger]
sIntegers = Trans.sIntegers

-- | Declare a named 'SReal'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sReal'
sReal :: String -> Symbolic SReal
sReal = Trans.sReal

-- | Declare an unnamed 'SReal'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sReal_'
sReal_ :: Symbolic SReal
sReal_ = Trans.sReal_

-- | Declare a list of 'SReal's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sReals'
sReals :: [String] -> Symbolic [SReal]
sReals = Trans.sReals

-- | Declare a named 'SFloat'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloat'
sFloat :: String -> Symbolic SFloat
sFloat = Trans.sFloat

-- | Declare an unnamed 'SFloat'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloat_'
sFloat_ :: Symbolic SFloat
sFloat_ = Trans.sFloat_

-- | Declare a list of 'SFloat's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloats'
sFloats :: [String] -> Symbolic [SFloat]
sFloats = Trans.sFloats

-- | Declare a named 'SDouble'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sDouble'
sDouble :: String -> Symbolic SDouble
sDouble = Trans.sDouble

-- | Declare an unnamed 'SDouble'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sDouble_'
sDouble_ :: Symbolic SDouble
sDouble_ = Trans.sDouble_

-- | Declare a list of 'SDouble's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sDoubles'
sDoubles :: [String] -> Symbolic [SDouble]
sDoubles = Trans.sDoubles

-- | Declare a named 'SFloatingPoint eb sb'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloatingPoint'
sFloatingPoint :: ValidFloat eb sb => String -> Symbolic (SFloatingPoint eb sb)
sFloatingPoint = Trans.sFloatingPoint

-- | Declare an unnamed 'SFloatingPoint' @eb@ @sb@
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloatingPoint_'
sFloatingPoint_ :: ValidFloat eb sb => Symbolic (SFloatingPoint eb sb)
sFloatingPoint_ = Trans.sFloatingPoint_

-- | Declare a list of 'SFloatingPoint' @eb@ @sb@'s
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloatingPoints'
sFloatingPoints :: ValidFloat eb sb => [String] -> Symbolic [SFloatingPoint eb sb]
sFloatingPoints = Trans.sFloatingPoints

-- | Declare a named 'SFPHalf'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPHalf'
sFPHalf :: String -> Symbolic SFPHalf
sFPHalf = Trans.sFPHalf

-- | Declare an unnamed 'SFPHalf'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPHalf_'
sFPHalf_ :: Symbolic SFPHalf
sFPHalf_ = Trans.sFPHalf_

-- | Declare a list of 'SFPHalf's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPHalfs'
sFPHalfs :: [String] -> Symbolic [SFPHalf]
sFPHalfs = Trans.sFPHalfs

-- | Declare a named 'SFPBFloat'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.SFPBFloat'
sFPBFloat :: String -> Symbolic SFPBFloat
sFPBFloat = Trans.sFPBFloat

-- | Declare an unnamed 'SFPBFloat'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.SFPBFloat'
sFPBFloat_ :: Symbolic SFPBFloat
sFPBFloat_ = Trans.sFPBFloat_

-- | Declare a list of 'SFPQuad's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPBFloats'
sFPBFloats :: [String] -> Symbolic [SFPBFloat]
sFPBFloats = Trans.sFPBFloats

-- | Declare a named 'SFPSingle'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPSingle'
sFPSingle :: String -> Symbolic SFPSingle
sFPSingle = Trans.sFPSingle

-- | Declare an unnamed 'SFPSingle'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPSingle_'
sFPSingle_ :: Symbolic SFPSingle
sFPSingle_ = Trans.sFPSingle_

-- | Declare a list of 'SFPSingle's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPSingles'
sFPSingles :: [String] -> Symbolic [SFPSingle]
sFPSingles = Trans.sFPSingles

-- | Declare a named 'SFPDouble'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPDouble'
sFPDouble :: String -> Symbolic SFPDouble
sFPDouble = Trans.sFPDouble

-- | Declare an unnamed 'SFPDouble'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPDouble_'
sFPDouble_ :: Symbolic SFPDouble
sFPDouble_ = Trans.sFPDouble_

-- | Declare a list of 'SFPDouble's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPDoubles'
sFPDoubles :: [String] -> Symbolic [SFPDouble]
sFPDoubles = Trans.sFPDoubles

-- | Declare a named 'SFPQuad'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPQuad'
sFPQuad :: String -> Symbolic SFPQuad
sFPQuad = Trans.sFPQuad

-- | Declare an unnamed 'SFPQuad'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPQuad_'
sFPQuad_ :: Symbolic SFPQuad
sFPQuad_ = Trans.sFPQuad_

-- | Declare a list of 'SFPQuad's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFPQuads'
sFPQuads :: [String] -> Symbolic [SFPQuad]
sFPQuads = Trans.sFPQuads

-- | Declare a named 'SChar'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sChar'
sChar :: String -> Symbolic SChar
sChar = Trans.sChar

-- | Declare an unnamed 'SChar'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sChar_'
sChar_ :: Symbolic SChar
sChar_ = Trans.sChar_

-- | Declare a list of 'SChar's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sChars'
sChars :: [String] -> Symbolic [SChar]
sChars = Trans.sChars

-- | Declare a named 'SString'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sString'
sString :: String -> Symbolic SString
sString = Trans.sString

-- | Declare an unnamed 'SString'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sString_'
sString_ :: Symbolic SString
sString_ = Trans.sString_

-- | Declare a list of 'SString's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sStrings'
sStrings :: [String] -> Symbolic [SString]
sStrings = Trans.sStrings

-- | Declare a named 'SList'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sList'
sList :: SymVal a => String -> Symbolic (SList a)
sList = Trans.sList

-- | Declare an unnamed 'SList'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sList_'
sList_ :: SymVal a => Symbolic (SList a)
sList_ = Trans.sList_

-- | Declare a list of 'SList's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sLists'
sLists :: SymVal a => [String] -> Symbolic [SList a]
sLists = Trans.sLists

-- | Declare a named tuple.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sTuple'
sTuple :: (SymTuple tup, SymVal tup) => String -> Symbolic (SBV tup)
sTuple = Trans.sTuple

-- | Declare an unnamed tuple.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sTuple_'
sTuple_ :: (SymTuple tup, SymVal tup) => Symbolic (SBV tup)
sTuple_ = Trans.sTuple_

-- | Declare a list of tuples.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sTuples'
sTuples :: (SymTuple tup, SymVal tup) => [String] -> Symbolic [SBV tup]
sTuples = Trans.sTuples

-- | Declare a named 'Data.SBV.SEither'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sEither'
sEither :: (SymVal a, SymVal b) => String -> Symbolic (SEither a b)
sEither = Trans.sEither

-- | Declare an unnamed 'Data.SBV.SEither'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sEither_'
sEither_ :: (SymVal a, SymVal b) => Symbolic (SEither a b)
sEither_ = Trans.sEither_

-- | Declare a list of 'Data.SBV.SEither' values.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sEithers'
sEithers :: (SymVal a, SymVal b) => [String] -> Symbolic [SEither a b]
sEithers = Trans.sEithers

-- | Declare a named 'Data.SBV.SRational'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sRational'
sRational :: String -> Symbolic SRational
sRational = Trans.sRational

-- | Declare an unnamed 'Data.SBV.SRational'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sRational_'
sRational_ :: Symbolic SRational
sRational_ = Trans.sRational_

-- | Declare a list of 'Data.SBV.SRational' values.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sRationals'
sRationals :: [String] -> Symbolic [SRational]
sRationals = Trans.sRationals

-- | Declare a named 'Data.SBV.SMaybe'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sMaybe'
sMaybe :: SymVal a => String -> Symbolic (SMaybe a)
sMaybe = Trans.sMaybe

-- | Declare an unnamed 'Data.SBV.SMaybe'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sMaybe_'
sMaybe_ :: SymVal a => Symbolic (SMaybe a)
sMaybe_ = Trans.sMaybe_

-- | Declare a list of 'Data.SBV.SMaybe' values.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sMaybes'
sMaybes :: SymVal a => [String] -> Symbolic [SMaybe a]
sMaybes = Trans.sMaybes

-- | Declare a named 'Data.SBV.SSet'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sSet'
sSet :: (Ord a, SymVal a) => String -> Symbolic (SSet a)
sSet = Trans.sSet

-- | Declare an unnamed 'Data.SBV.SSet'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sSet_'
sSet_ :: (Ord a, SymVal a) => Symbolic (SSet a)
sSet_ = Trans.sSet_

-- | Declare a list of 'Data.SBV.SSet' values.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sSets'
sSets :: (Ord a, SymVal a) => [String] -> Symbolic [SSet a]
sSets = Trans.sSets

-- | Form the symbolic conjunction of a given list of boolean conditions. Useful in expressing
-- problems with constraints, like the following:
--
-- @
--   sat $ do [x, y, z] <- sIntegers [\"x\", \"y\", \"z\"]
--            solve [x .> 5, y + z .< x]
-- @
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.solve'
solve :: [SBool] -> Symbolic SBool
solve = Trans.solve

-- | Introduce a soft assertion, with an optional penalty
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.assertWithPenalty'
assertWithPenalty :: String -> SBool -> Penalty -> Symbolic ()
assertWithPenalty = Trans.assertWithPenalty

-- | Minimize a named metric
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.minimize'
minimize :: Metric a => String -> SBV a -> Symbolic ()
minimize = Trans.minimize

-- | Maximize a named metric
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.maximize'
maximize :: Metric a => String -> SBV a -> Symbolic ()
maximize = Trans.maximize

-- Data.SBV.Core.Symbolic:

-- | Convert a symbolic value to an SV, inside the Symbolic monad
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.svToSymSV'
svToSymSV :: SVal -> Symbolic SV
svToSymSV = Trans.svToSymSV

-- | Run a symbolic computation, and return a extra value paired up with the 'Result'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.runSymbolic'
runSymbolic :: SMTConfig -> SBVRunMode -> Symbolic a -> IO (a, Result)
runSymbolic = Trans.runSymbolic

-- | Add a new option
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.addNewSMTOption'
addNewSMTOption :: SMTOption -> Symbolic ()
addNewSMTOption = Trans.addNewSMTOption

-- | Handling constraints
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.imposeConstraint'
imposeConstraint :: Bool -> [(String, String)] -> SVal -> Symbolic ()
imposeConstraint = Trans.imposeConstraint

-- | Add an optimization goal
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.addSValOptGoal'
addSValOptGoal :: Objective SVal -> Symbolic ()
addSValOptGoal = Trans.addSValOptGoal

-- | Mark an interim result as an output. Useful when constructing Symbolic programs
-- that return multiple values, or when the result is programmatically computed.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.outputSVal'
outputSVal :: SVal -> Symbolic ()
outputSVal = Trans.outputSVal

-- | Capturing non-matching instances for better error messages, conversions from sized
type FromSizedErr (arg :: Type) =     'Text "fromSized: Cannot convert from type: " ':<>: 'ShowType arg
                                ':$$: 'Text "           Source type must be one of SInt N, SWord N, IntN N, WordN N"
                                ':$$: 'Text "           where N is 8, 16, 32, or 64."

-- | Capturing non-matching instances for better error messages, conversions to sized
type ToSizedErr (arg :: Type) =      'Text "toSized: Cannot convert from type: " ':<>: 'ShowType arg
                              ':$$: 'Text "          Source type must be one of Int8/16/32/64"
                              ':$$: 'Text "                                  OR Word8/16/32/64"
                              ':$$: 'Text "                                  OR their symbolic variants."

-- | Capture the correspondence between sized and fixed-sized BVs
type family FromSized (t :: Type) :: Type where
   FromSized (WordN  8) = Word8
   FromSized (WordN 16) = Word16
   FromSized (WordN 32) = Word32
   FromSized (WordN 64) = Word64
   FromSized (IntN   8) = Int8
   FromSized (IntN  16) = Int16
   FromSized (IntN  32) = Int32
   FromSized (IntN  64) = Int64
   FromSized (SWord  8) = SWord8
   FromSized (SWord 16) = SWord16
   FromSized (SWord 32) = SWord32
   FromSized (SWord 64) = SWord64
   FromSized (SInt   8) = SInt8
   FromSized (SInt  16) = SInt16
   FromSized (SInt  32) = SInt32
   FromSized (SInt  64) = SInt64

-- | Capture the correspondence, in terms of a constraint
type family FromSizedCstr (t :: Type) :: Constraint where
   FromSizedCstr (WordN  8) = ()
   FromSizedCstr (WordN 16) = ()
   FromSizedCstr (WordN 32) = ()
   FromSizedCstr (WordN 64) = ()
   FromSizedCstr (IntN   8) = ()
   FromSizedCstr (IntN  16) = ()
   FromSizedCstr (IntN  32) = ()
   FromSizedCstr (IntN  64) = ()
   FromSizedCstr (SWord  8) = ()
   FromSizedCstr (SWord 16) = ()
   FromSizedCstr (SWord 32) = ()
   FromSizedCstr (SWord 64) = ()
   FromSizedCstr (SInt   8) = ()
   FromSizedCstr (SInt  16) = ()
   FromSizedCstr (SInt  32) = ()
   FromSizedCstr (SInt  64) = ()
   FromSizedCstr arg        = TypeError (FromSizedErr arg)

-- | Conversion from a sized BV to a fixed-sized bit-vector.
class FromSizedBV a where
   -- | Convert a sized bit-vector to the corresponding fixed-sized bit-vector,
   -- for instance 'SWord 16' to 'SWord16'. See also 'toSized'.
   fromSized :: a -> FromSized a

   default fromSized :: (Num (FromSized a), Integral a) => a -> FromSized a
   fromSized = fromIntegral

instance {-# OVERLAPPING  #-} FromSizedBV (WordN   8)
instance {-# OVERLAPPING  #-} FromSizedBV (WordN  16)
instance {-# OVERLAPPING  #-} FromSizedBV (WordN  32)
instance {-# OVERLAPPING  #-} FromSizedBV (WordN  64)
instance {-# OVERLAPPING  #-} FromSizedBV (IntN    8)
instance {-# OVERLAPPING  #-} FromSizedBV (IntN   16)
instance {-# OVERLAPPING  #-} FromSizedBV (IntN   32)
instance {-# OVERLAPPING  #-} FromSizedBV (IntN   64)
instance {-# OVERLAPPING  #-} FromSizedBV (SWord   8) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} FromSizedBV (SWord  16) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} FromSizedBV (SWord  32) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} FromSizedBV (SWord  64) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} FromSizedBV (SInt    8) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} FromSizedBV (SInt   16) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} FromSizedBV (SInt   32) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} FromSizedBV (SInt   64) where fromSized = Trans.sFromIntegral
instance {-# OVERLAPPABLE #-} FromSizedCstr arg => FromSizedBV arg where fromSized = error "unreachable"

-- | Capture the correspondence between fixed-sized and sized BVs
type family ToSized (t :: Type) :: Type where
   ToSized Word8   = WordN  8
   ToSized Word16  = WordN 16
   ToSized Word32  = WordN 32
   ToSized Word64  = WordN 64
   ToSized Int8    = IntN   8
   ToSized Int16   = IntN  16
   ToSized Int32   = IntN  32
   ToSized Int64   = IntN  64
   ToSized SWord8  = SWord  8
   ToSized SWord16 = SWord 16
   ToSized SWord32 = SWord 32
   ToSized SWord64 = SWord 64
   ToSized SInt8   = SInt   8
   ToSized SInt16  = SInt  16
   ToSized SInt32  = SInt  32
   ToSized SInt64  = SInt  64

-- | Capture the correspondence in terms of a constraint
type family ToSizedCstr (t :: Type) :: Constraint where
   ToSizedCstr Word8   = ()
   ToSizedCstr Word16  = ()
   ToSizedCstr Word32  = ()
   ToSizedCstr Word64  = ()
   ToSizedCstr Int8    = ()
   ToSizedCstr Int16   = ()
   ToSizedCstr Int32   = ()
   ToSizedCstr Int64   = ()
   ToSizedCstr SWord8  = ()
   ToSizedCstr SWord16 = ()
   ToSizedCstr SWord32 = ()
   ToSizedCstr SWord64 = ()
   ToSizedCstr SInt8   = ()
   ToSizedCstr SInt16  = ()
   ToSizedCstr SInt32  = ()
   ToSizedCstr SInt64  = ()
   ToSizedCstr arg     = TypeError (ToSizedErr arg)

-- | Conversion from a fixed-sized BV to a sized bit-vector.
class ToSizedBV a where
   -- | Convert a fixed-sized bit-vector to the corresponding sized bit-vector,
   -- for instance 'SWord16' to 'SWord 16'. See also 'fromSized'.
   toSized :: a -> ToSized a

   default toSized :: (Num (ToSized a), Integral a) => (a -> ToSized a)
   toSized = fromIntegral

instance {-# OVERLAPPING  #-} ToSizedBV Word8
instance {-# OVERLAPPING  #-} ToSizedBV Word16
instance {-# OVERLAPPING  #-} ToSizedBV Word32
instance {-# OVERLAPPING  #-} ToSizedBV Word64
instance {-# OVERLAPPING  #-} ToSizedBV Int8
instance {-# OVERLAPPING  #-} ToSizedBV Int16
instance {-# OVERLAPPING  #-} ToSizedBV Int32
instance {-# OVERLAPPING  #-} ToSizedBV Int64
instance {-# OVERLAPPING  #-} ToSizedBV SWord8  where toSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} ToSizedBV SWord16 where toSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} ToSizedBV SWord32 where toSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} ToSizedBV SWord64 where toSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} ToSizedBV SInt8   where toSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} ToSizedBV SInt16  where toSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} ToSizedBV SInt32  where toSized = Trans.sFromIntegral
instance {-# OVERLAPPING  #-} ToSizedBV SInt64  where toSized = Trans.sFromIntegral
instance {-# OVERLAPPABLE #-} ToSizedCstr arg => ToSizedBV arg where toSized = error "unreachable"
