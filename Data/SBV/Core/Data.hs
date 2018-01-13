-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.Data
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}

module Data.SBV.Core.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64, SInteger, SReal, SFloat, SDouble
 , nan, infinity, sNaN, sInfinity, RoundingMode(..), SRoundingMode
 , sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive, sRoundTowardNegative, sRoundTowardZero
 , sRNE, sRNA, sRTP, sRTN, sRTZ
 , SymWord(..)
 , CW(..), CWVal(..), AlgReal(..), ExtCW(..), GeneralizedCW(..), isRegularCW, cwSameType, cwToBool
 , mkConstCW ,liftCW2, mapCW, mapCW2
 , SW(..), trueSW, falseSW, trueCW, falseCW, normCW
 , SVal(..)
 , SBV(..), NodeId(..), mkSymSBV
 , ArrayContext(..), ArrayInfo, SymArray(..), SFunArray(..), mkSFunArray, SArray(..)
 , sbvToSW, sbvToSymSW, forceSWArg
 , SBVExpr(..), newExpr
 , cache, Cached, uncache, uncacheAI, HasKind(..)
 , Op(..), PBOp(..), FPOp(..), NamedSymVar, getTableIndex
 , SBVPgm(..), Symbolic, runSymbolic, State, getPathCondition, extendPathCondition
 , inSMTMode, SBVRunMode(..), Kind(..), Outputtable(..), Result(..)
 , SolverContext(..), internalVariable, internalConstraint, isCodeGenMode
 , SBVType(..), newUninterpreted, addAxiom
 , Quantifier(..), needsExistentials
 , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension, smtLibReservedNames
 , SolverCapabilities(..)
 , extractSymbolicSimulationState
 , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..)
 , declNewSArray, declNewSFunArray
 , OptimizeStyle(..), Penalty(..), Objective(..)
 , QueryState(..), Query(..), SMTProblem(..)
 ) where

import GHC.Generics (Generic)

import Control.DeepSeq      (NFData(..))
import Control.Monad.Reader (ask)
import Control.Monad.Trans  (liftIO)
import Data.Int             (Int8, Int16, Int32, Int64)
import Data.Word            (Word8, Word16, Word32, Word64)
import Data.List            (elemIndex)

import qualified Data.Generics as G    (Data(..))

import System.Random

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Operations

import Data.SBV.Control.Types

import Data.SBV.SMT.SMTLibNames

import Data.SBV.Utils.Lib
import Data.SBV.Utils.Boolean

-- | Get the current path condition
getPathCondition :: State -> SBool
getPathCondition st = SBV (getSValPathCondition st)

-- | Extend the path condition with the given test value.
extendPathCondition :: State -> (SBool -> SBool) -> State
extendPathCondition st f = extendSValPathCondition st (unSBV . f . SBV)

-- | The "Symbolic" value. The parameter 'a' is phantom, but is
-- extremely important in keeping the user interface strongly typed.
newtype SBV a = SBV { unSBV :: SVal }
              deriving (Generic, NFData)

-- | A symbolic boolean/bit
type SBool   = SBV Bool

-- | 8-bit unsigned symbolic value
type SWord8  = SBV Word8

-- | 16-bit unsigned symbolic value
type SWord16 = SBV Word16

-- | 32-bit unsigned symbolic value
type SWord32 = SBV Word32

-- | 64-bit unsigned symbolic value
type SWord64 = SBV Word64

-- | 8-bit signed symbolic value, 2's complement representation
type SInt8   = SBV Int8

-- | 16-bit signed symbolic value, 2's complement representation
type SInt16  = SBV Int16

-- | 32-bit signed symbolic value, 2's complement representation
type SInt32  = SBV Int32

-- | 64-bit signed symbolic value, 2's complement representation
type SInt64  = SBV Int64

-- | Infinite precision signed symbolic value
type SInteger = SBV Integer

-- | Infinite precision symbolic algebraic real value
type SReal = SBV AlgReal

-- | IEEE-754 single-precision floating point numbers
type SFloat = SBV Float

-- | IEEE-754 double-precision floating point numbers
type SDouble = SBV Double

-- | Not-A-Number for 'Double' and 'Float'. Surprisingly, Haskell
-- Prelude doesn't have this value defined, so we provide it here.
nan :: Floating a => a
nan = 0/0

-- | Infinity for 'Double' and 'Float'. Surprisingly, Haskell
-- Prelude doesn't have this value defined, so we provide it here.
infinity :: Floating a => a
infinity = 1/0

-- | Symbolic variant of Not-A-Number. This value will inhabit both
-- 'SDouble' and 'SFloat'.
sNaN :: (Floating a, SymWord a) => SBV a
sNaN = literal nan

-- | Symbolic variant of infinity. This value will inhabit both
-- 'SDouble' and 'SFloat'.
sInfinity :: (Floating a, SymWord a) => SBV a
sInfinity = literal infinity

-- Boolean combinators
instance Boolean SBool where
  true  = SBV (svBool True)
  false = SBV (svBool False)
  bnot (SBV b) = SBV (svNot b)
  SBV a &&& SBV b = SBV (svAnd a b)
  SBV a ||| SBV b = SBV (svOr a b)
  SBV a <+> SBV b = SBV (svXOr a b)

-- | 'RoundingMode' can be used symbolically
instance SymWord RoundingMode

-- | The symbolic variant of 'RoundingMode'
type SRoundingMode = SBV RoundingMode

-- | Symbolic variant of 'RoundNearestTiesToEven'
sRoundNearestTiesToEven :: SRoundingMode
sRoundNearestTiesToEven = literal RoundNearestTiesToEven

-- | Symbolic variant of 'RoundNearestTiesToAway'
sRoundNearestTiesToAway :: SRoundingMode
sRoundNearestTiesToAway = literal RoundNearestTiesToAway

-- | Symbolic variant of 'RoundNearestPositive'
sRoundTowardPositive :: SRoundingMode
sRoundTowardPositive = literal RoundTowardPositive

-- | Symbolic variant of 'RoundTowardNegative'
sRoundTowardNegative :: SRoundingMode
sRoundTowardNegative = literal RoundTowardNegative

-- | Symbolic variant of 'RoundTowardZero'
sRoundTowardZero :: SRoundingMode
sRoundTowardZero = literal RoundTowardZero

-- | Alias for 'sRoundNearestTiesToEven'
sRNE :: SRoundingMode
sRNE = sRoundNearestTiesToEven

-- | Alias for 'sRoundNearestTiesToAway'
sRNA :: SRoundingMode
sRNA = sRoundNearestTiesToAway

-- | Alias for 'sRoundTowardPositive'
sRTP :: SRoundingMode
sRTP = sRoundTowardPositive

-- | Alias for 'sRoundTowardNegative'
sRTN :: SRoundingMode
sRTN = sRoundTowardNegative

-- | Alias for 'sRoundTowardZero'
sRTZ :: SRoundingMode
sRTZ = sRoundTowardZero

-- Not particularly "desirable," when the value is symbolic, but we do need this
-- instance as otherwise we cannot simply evaluate Haskell functions that return
-- symbolic values and have their constant values printed easily!
instance Show (SBV a) where
  show (SBV sv) = show sv

-- Equality constraint on SBV values. Not desirable since we can't really compare two
-- symbolic values, but will do. Note that we do need this instance since we want
-- Bits as a class for SBV that we implement, which necessiates the Eq class.
instance Eq (SBV a) where
  SBV a == SBV b = a == b
  SBV a /= SBV b = a /= b

instance HasKind (SBV a) where
  kindOf (SBV (SVal k _)) = k

-- | Convert a symbolic value to a symbolic-word
sbvToSW :: State -> SBV a -> IO SW
sbvToSW st (SBV s) = svToSW st s

-------------------------------------------------------------------------
-- * Symbolic Computations
-------------------------------------------------------------------------

-- | Create a symbolic variable.
mkSymSBV :: forall a. Maybe Quantifier -> Kind -> Maybe String -> Symbolic (SBV a)
mkSymSBV mbQ k mbNm = SBV <$> (ask >>= liftIO . svMkSymVar mbQ k mbNm)

-- | Convert a symbolic value to an SW, inside the Symbolic monad
sbvToSymSW :: SBV a -> Symbolic SW
sbvToSymSW sbv = do
        st <- ask
        liftIO $ sbvToSW st sbv

-- | Actions we can do in a context: Either at problem description
-- time or while we are dynamically querying. 'Symbolic' and 'Query' are
-- two instances of this class. Note that we use this mechanism
-- internally and do not export it from SBV.
class SolverContext m where
   -- | Add a constraint, any satisfying instance must satisfy this condition
   constrain       :: SBool -> m ()
   -- | Add a named constraint. The name is used in unsat-core extraction.
   namedConstraint :: String -> SBool -> m ()
   -- | Set info. Example: @setInfo ":status" ["unsat"]@.
   setInfo :: String -> [String] -> m ()
   -- | Set an option.
   setOption :: SMTOption -> m ()
   -- | Set the logic.
   setLogic :: Logic -> m ()
   -- | Set a solver time-out value, in milli-seconds. This function
   -- essentially translates to the SMTLib call @(set-info :timeout val)@,
   -- and your backend solver may or may not support it! The amount given
   -- is in milliseconds. Also see the function 'timeOut' for finer level
   -- control of time-outs, directly from SBV.
   setTimeOut :: Integer -> m ()

   -- time-out, logic, and info are  simply options in our implementation, so default implementation suffices
   setTimeOut t = setOption $ OptionKeyword ":timeout" [show t]
   setLogic     = setOption . SetLogic
   setInfo    k = setOption . SetInfo k

-- | A class representing what can be returned from a symbolic computation.
class Outputtable a where
  -- | Mark an interim result as an output. Useful when constructing Symbolic programs
  -- that return multiple values, or when the result is programmatically computed.
  output :: a -> Symbolic a

instance Outputtable (SBV a) where
  output i = do
          outputSVal (unSBV i)
          return i

instance Outputtable a => Outputtable [a] where
  output = mapM output

instance Outputtable () where
  output = return

instance (Outputtable a, Outputtable b) => Outputtable (a, b) where
  output = mlift2 (,) output output

instance (Outputtable a, Outputtable b, Outputtable c) => Outputtable (a, b, c) where
  output = mlift3 (,,) output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d) => Outputtable (a, b, c, d) where
  output = mlift4 (,,,) output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e) => Outputtable (a, b, c, d, e) where
  output = mlift5 (,,,,) output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f) => Outputtable (a, b, c, d, e, f) where
  output = mlift6 (,,,,,) output output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f, Outputtable g) => Outputtable (a, b, c, d, e, f, g) where
  output = mlift7 (,,,,,,) output output output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f, Outputtable g, Outputtable h) => Outputtable (a, b, c, d, e, f, g, h) where
  output = mlift8 (,,,,,,,) output output output output output output output output

-------------------------------------------------------------------------------
-- * Symbolic Words
-------------------------------------------------------------------------------
-- | A 'SymWord' is a potential symbolic bitvector that can be created instances of
-- to be fed to a symbolic program. Note that these methods are typically not needed
-- in casual uses with 'prove', 'sat', 'allSat' etc, as default instances automatically
-- provide the necessary bits.
class (HasKind a, Ord a) => SymWord a where
  -- | Create a user named input (universal)
  forall :: String -> Symbolic (SBV a)
  -- | Create an automatically named input
  forall_ :: Symbolic (SBV a)
  -- | Get a bunch of new words
  mkForallVars :: Int -> Symbolic [SBV a]
  -- | Create an existential variable
  exists  :: String -> Symbolic (SBV a)
  -- | Create an automatically named existential variable
  exists_ :: Symbolic (SBV a)
  -- | Create a bunch of existentials
  mkExistVars :: Int -> Symbolic [SBV a]
  -- | Create a free variable, universal in a proof, existential in sat
  free :: String -> Symbolic (SBV a)
  -- | Create an unnamed free variable, universal in proof, existential in sat
  free_ :: Symbolic (SBV a)
  -- | Create a bunch of free vars
  mkFreeVars :: Int -> Symbolic [SBV a]
  -- | Similar to free; Just a more convenient name
  symbolic  :: String -> Symbolic (SBV a)
  -- | Similar to mkFreeVars; but automatically gives names based on the strings
  symbolics :: [String] -> Symbolic [SBV a]
  -- | Turn a literal constant to symbolic
  literal :: a -> SBV a
  -- | Extract a literal, if the value is concrete
  unliteral :: SBV a -> Maybe a
  -- | Extract a literal, from a CW representation
  fromCW :: CW -> a
  -- | Is the symbolic word concrete?
  isConcrete :: SBV a -> Bool
  -- | Is the symbolic word really symbolic?
  isSymbolic :: SBV a -> Bool
  -- | Does it concretely satisfy the given predicate?
  isConcretely :: SBV a -> (a -> Bool) -> Bool
  -- | One stop allocator
  mkSymWord :: Maybe Quantifier -> Maybe String -> Symbolic (SBV a)

  -- minimal complete definition:: Nothing.
  -- Giving no instances is ok when defining an uninterpreted/enumerated sort, but otherwise you really
  -- want to define: literal, fromCW, mkSymWord
  forall   = mkSymWord (Just ALL) . Just
  forall_  = mkSymWord (Just ALL)   Nothing
  exists   = mkSymWord (Just EX)  . Just
  exists_  = mkSymWord (Just EX)    Nothing
  free     = mkSymWord Nothing    . Just
  free_    = mkSymWord Nothing      Nothing
  mkForallVars n = mapM (const forall_) [1 .. n]
  mkExistVars n  = mapM (const exists_) [1 .. n]
  mkFreeVars n   = mapM (const free_)   [1 .. n]
  symbolic       = free
  symbolics      = mapM symbolic
  unliteral (SBV (SVal _ (Left c)))  = Just $ fromCW c
  unliteral _                        = Nothing
  isConcrete (SBV (SVal _ (Left _))) = True
  isConcrete _                       = False
  isSymbolic = not . isConcrete
  isConcretely s p
    | Just i <- unliteral s = p i
    | True                  = False

  default literal :: Show a => a -> SBV a
  literal x = let k@(KUserSort  _ conts) = kindOf x
                  sx                     = show x
                  mbIdx = case conts of
                            Right xs -> sx `elemIndex` xs
                            _        -> Nothing
              in SBV $ SVal k (Left (CW k (CWUserSort (mbIdx, sx))))

  default fromCW :: Read a => CW -> a
  fromCW (CW _ (CWUserSort (_, s))) = read s
  fromCW cw                         = error $ "Cannot convert CW " ++ show cw ++ " to kind " ++ show (kindOf (undefined :: a))

  default mkSymWord :: (Read a, G.Data a) => Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
  mkSymWord mbQ mbNm = SBV <$> (ask >>= liftIO . svMkSymVar mbQ k mbNm)
    where k = constructUKind (undefined :: a)

instance (Random a, SymWord a) => Random (SBV a) where
  randomR (l, h) g = case (unliteral l, unliteral h) of
                       (Just lb, Just hb) -> let (v, g') = randomR (lb, hb) g in (literal (v :: a), g')
                       _                  -> error "SBV.Random: Cannot generate random values with symbolic bounds"
  random         g = let (v, g') = random g in (literal (v :: a) , g')
---------------------------------------------------------------------------------
-- * Symbolic Arrays
---------------------------------------------------------------------------------

-- | Flat arrays of symbolic values
-- An @array a b@ is an array indexed by the type @'SBV' a@, with elements of type @'SBV' b@.
--
-- While it's certainly possible for user to create instances of 'SymArray', the
-- 'SArray' and 'SFunArray' instances already provided should cover most use cases
-- in practice. (There are some differences between these models, however, see the corresponding
-- declaration.)
--
--
-- Minimal complete definition: All methods are required, no defaults.
class SymArray array where
  -- | Create a new anonymous array
  newArray_      :: (HasKind a, HasKind b) => Symbolic (array a b)
  -- | Create a named new array
  newArray       :: (HasKind a, HasKind b) => String -> Symbolic (array a b)
  -- | Read the array element at @a@
  readArray      :: array a b -> SBV a -> SBV b
  -- | Update the element at @a@ to be @b@
  writeArray     :: SymWord b => array a b -> SBV a -> SBV b -> array a b
  -- | Merge two given arrays on the symbolic condition
  -- Intuitively: @mergeArrays cond a b = if cond then a else b@.
  -- Merging pushes the if-then-else choice down on to elements
  mergeArrays    :: SymWord b => SBV Bool -> array a b -> array a b -> array a b

-- | Arrays implemented in terms of SMT-arrays: <http://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml>
--
--   * Maps directly to SMT-lib arrays
--
--   * Reading from an unintialized value is OK and yields an unspecified result
--
--   * Can check for equality of these arrays
--
--   * Cannot quick-check theorems using @SArray@ values
--
--   * Typically slower as it heavily relies on SMT-solving for the array theory
--
newtype SArray a b = SArray { unSArray :: SArr }

instance (HasKind a, HasKind b) => Show (SArray a b) where
  show SArray{} = "SArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

instance SymArray SArray where
  newArray_                                      = declNewSArray (\t -> "array_" ++ show t)
  newArray n                                     = declNewSArray (const n)
  readArray   (SArray arr) (SBV a)               = SBV (readSArr arr a)
  writeArray  (SArray arr) (SBV a)    (SBV b)    = SArray (writeSArr arr a b)
  mergeArrays (SBV t)      (SArray a) (SArray b) = SArray (mergeSArr t a b)

-- | Declare a new symbolic array, with a potential initial value
declNewSArray :: forall a b. (HasKind a, HasKind b) => (Int -> String) -> Symbolic (SArray a b)
declNewSArray mkNm = SArray <$> newSArr (aknd, bknd) mkNm
 where aknd = kindOf (undefined :: a)
       bknd = kindOf (undefined :: b)

-- | Declare a new functional symbolic array. Note that a read from an uninitialized cell will result in an error.
declNewSFunArray :: forall a b. (HasKind a, HasKind b) => Maybe String -> Symbolic (SFunArray a b)
declNewSFunArray mbNm = return $ SFunArray $ error . msg mbNm
  where msg Nothing   i = "Reading from an uninitialized array entry, index: " ++ show i
        msg (Just nm) i = "Array " ++ show nm ++ ": Reading from an uninitialized array entry, index: " ++ show i

-- | Arrays implemented internally as functions
--
--    * Internally handled by the library and not mapped to SMT-Lib
--
--    * Reading an uninitialized value is considered an error (will throw exception)
--
--    * Cannot check for equality (internally represented as functions)
--
--    * Can quick-check
--
--    * Typically faster as it gets compiled away during translation
--
newtype SFunArray a b = SFunArray (SBV a -> SBV b)

instance (HasKind a, HasKind b) => Show (SFunArray a b) where
  show (SFunArray _) = "SFunArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

-- | Lift a function to an array. Useful for creating arrays in a pure context. (Otherwise use `newArray`.)
mkSFunArray :: (SBV a -> SBV b) -> SFunArray a b
mkSFunArray = SFunArray

-- | Internal representation of a symbolic simulation result
newtype SMTProblem = SMTProblem {smtLibPgm :: SMTConfig -> SMTLibPgm} -- ^ SMTLib representation, given the config
