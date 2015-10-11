-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Data
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE NamedFieldPuns        #-}

module Data.SBV.BitVectors.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64, SInteger, SReal, SFloat, SDouble
 , nan, infinity, sNaN, sInfinity, RoundingMode(..), SRoundingMode
 , sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive, sRoundTowardNegative, sRoundTowardZero
 , sRNE, sRNA, sRTP, sRTN, sRTZ
 , SymWord(..)
 , CW(..), CWVal(..), AlgReal(..), cwSameType, cwIsBit, cwToBool
 , mkConstCW ,liftCW2, mapCW, mapCW2
 , SW(..), trueSW, falseSW, trueCW, falseCW, normCW
 , SVal(..)
 , SBV(..), NodeId(..), mkSymSBV
 , ArrayContext(..), ArrayInfo, SymArray(..), SFunArray(..), mkSFunArray, SArray(..)
 , sbvToSW, sbvToSymSW, forceSWArg
 , SBVExpr(..), newExpr
 , cache, Cached, uncache, uncacheAI, HasKind(..)
 , Op(..), FPOp(..), NamedSymVar, getTableIndex
 , SBVPgm(..), Symbolic, runSymbolic, runSymbolic', State, getPathCondition, extendPathCondition
 , inProofMode, SBVRunMode(..), Kind(..), Outputtable(..), Result(..)
 , Logic(..), SMTLibLogic(..)
 , getTraceInfo, getConstraints, addConstraint, internalVariable, internalConstraint, isCodeGenMode
 , SBVType(..), newUninterpreted, addAxiom
 , Quantifier(..), needsExistentials
 , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension
 , SolverCapabilities(..)
 , extractSymbolicSimulationState
 , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..), getSBranchRunConfig
 , declNewSArray, declNewSFunArray
 ) where

import Control.DeepSeq      (NFData(..))
import Control.Monad.Reader (ask)
import Control.Monad.Trans  (liftIO)
import Data.Int             (Int8, Int16, Int32, Int64)
import Data.Word            (Word8, Word16, Word32, Word64)
import Data.List            (elemIndex)
import Data.Maybe           (fromMaybe)

import qualified Data.Generics as G    (Data(..))

import System.Random

import Data.SBV.BitVectors.AlgReals
import Data.SBV.Utils.Lib

import Data.SBV.BitVectors.Kind
import Data.SBV.BitVectors.Concrete
import Data.SBV.BitVectors.Symbolic

-- | A class for capturing values that have a sign and a size (finite or infinite)
-- minimal complete definition: kindOf. This class can be automatically derived
-- for data-types that have a 'Data' instance; this is useful for creating uninterpreted
-- sorts.
class HasKind a where
  kindOf          :: a -> Kind
  hasSign         :: a -> Bool
  intSizeOf       :: a -> Int
  isBoolean       :: a -> Bool
  isBounded       :: a -> Bool   -- NB. This really means word/int; i.e., Real/Float will test False
  isReal          :: a -> Bool
  isFloat         :: a -> Bool
  isDouble        :: a -> Bool
  isInteger       :: a -> Bool
  isUninterpreted :: a -> Bool
  showType        :: a -> String
  -- defaults
  hasSign x = kindHasSign (kindOf x)
  intSizeOf x = case kindOf x of
                  KBool         -> error "SBV.HasKind.intSizeOf((S)Bool)"
                  KBounded _ s  -> s
                  KUnbounded    -> error "SBV.HasKind.intSizeOf((S)Integer)"
                  KReal         -> error "SBV.HasKind.intSizeOf((S)Real)"
                  KFloat        -> error "SBV.HasKind.intSizeOf((S)Float)"
                  KDouble       -> error "SBV.HasKind.intSizeOf((S)Double)"
                  KUserSort s _ -> error $ "SBV.HasKind.intSizeOf: Uninterpreted sort: " ++ s
  isBoolean       x | KBool{}      <- kindOf x = True
                    | True                     = False
  isBounded       x | KBounded{}   <- kindOf x = True
                    | True                     = False
  isReal          x | KReal{}      <- kindOf x = True
                    | True                     = False
  isFloat         x | KFloat{}     <- kindOf x = True
                    | True                     = False
  isDouble        x | KDouble{}    <- kindOf x = True
                    | True                     = False
  isInteger       x | KUnbounded{} <- kindOf x = True
                    | True                     = False
  isUninterpreted x | KUserSort{}  <- kindOf x = True
                    | True                     = False
  showType = show . kindOf

  -- default signature for uninterpreted/enumerated kinds
  default kindOf :: (Read a, G.Data a) => a -> Kind
  kindOf = constructUKind

instance HasKind Bool    where kindOf _ = KBool
instance HasKind Int8    where kindOf _ = KBounded True  8
instance HasKind Word8   where kindOf _ = KBounded False 8
instance HasKind Int16   where kindOf _ = KBounded True  16
instance HasKind Word16  where kindOf _ = KBounded False 16
instance HasKind Int32   where kindOf _ = KBounded True  32
instance HasKind Word32  where kindOf _ = KBounded False 32
instance HasKind Int64   where kindOf _ = KBounded True  64
instance HasKind Word64  where kindOf _ = KBounded False 64
instance HasKind Integer where kindOf _ = KUnbounded
instance HasKind AlgReal where kindOf _ = KReal
instance HasKind Float   where kindOf _ = KFloat
instance HasKind Double  where kindOf _ = KDouble

instance HasKind Kind where
  kindOf = id

instance HasKind CW where
  kindOf = cwKind

instance HasKind SW where
  kindOf (SW k _) = k

-- | Get the current path condition
getPathCondition :: State -> SBool
getPathCondition st = SBV (getSValPathCondition st)

-- | Extend the path condition with the given test value.
extendPathCondition :: State -> (SBool -> SBool) -> State
extendPathCondition st f = extendSValPathCondition st (unSBV . f . SBV)

-- | The "Symbolic" value. The parameter 'a' is phantom, but is
-- extremely important in keeping the user interface strongly typed.
newtype SBV a = SBV { unSBV :: SVal }

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

-- | 'RoundingMode' can be used symbolically
instance SymWord RoundingMode

-- | 'RoundingMode' kind
instance HasKind RoundingMode

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

-- Not particularly "desirable", but will do if needed
instance Show (SBV a) where
  show (SBV sv) = show sv

-- Equality constraint on SBV values. Not desirable since we can't really compare two
-- symbolic values, but will do.
instance Eq (SBV a) where
  SBV a == SBV b = a == b
  SBV a /= SBV b = a /= b

instance HasKind a => HasKind (SBV a) where
  kindOf (SBV (SVal k _)) = k

-- | Convert a symbolic value to a symbolic-word
sbvToSW :: State -> SBV a -> IO SW
sbvToSW st (SBV s) = svToSW st s

-------------------------------------------------------------------------
-- * Symbolic Computations
-------------------------------------------------------------------------

-- | Create a symbolic variable.
mkSymSBV :: forall a. SymWord a => Maybe Quantifier -> Kind -> Maybe String -> Symbolic (SBV a)
mkSymSBV mbQ k mbNm = fmap SBV (svMkSymVar mbQ k mbNm)

-- | Convert a symbolic value to an SW, inside the Symbolic monad
sbvToSymSW :: SBV a -> Symbolic SW
sbvToSymSW sbv = do
        st <- ask
        liftIO $ sbvToSW st sbv

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
  literal x = let k@(KUserSort  _ (conts, _)) = kindOf x
                  sx                          = show x
                  mbIdx = case conts of
                            Right xs -> sx `elemIndex` xs
                            _        -> Nothing
              in SBV $ SVal k (Left (CW k (CWUserSort (mbIdx, sx))))

  default fromCW :: Read a => CW -> a
  fromCW (CW _ (CWUserSort (_, s))) = read s
  fromCW cw                         = error $ "Cannot convert CW " ++ show cw ++ " to kind " ++ show (kindOf (undefined :: a))

  default mkSymWord :: (Read a, G.Data a) => Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
  mkSymWord mbQ mbNm = SBV <$> mkSValUserSort k mbQ mbNm
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
-- An @array a b@ is an array indexed by the type @'SBV' a@, with elements of type @'SBV' b@
-- If an initial value is not provided in 'newArray_' and 'newArray' methods, then the elements
-- are left unspecified, i.e., the solver is free to choose any value. This is the right thing
-- to do if arrays are used as inputs to functions to be verified, typically. 
--
-- While it's certainly possible for user to create instances of 'SymArray', the
-- 'SArray' and 'SFunArray' instances already provided should cover most use cases
-- in practice. (There are some differences between these models, however, see the corresponding
-- declaration.)
--
--
-- Minimal complete definition: All methods are required, no defaults.
class SymArray array where
  -- | Create a new array, with an optional initial value
  newArray_      :: (HasKind a, HasKind b) => Maybe (SBV b) -> Symbolic (array a b)
  -- | Create a named new array, with an optional initial value
  newArray       :: (HasKind a, HasKind b) => String -> Maybe (SBV b) -> Symbolic (array a b)
  -- | Read the array element at @a@
  readArray      :: array a b -> SBV a -> SBV b
  -- | Reset all the elements of the array to the value @b@
  resetArray     :: SymWord b => array a b -> SBV b -> array a b
  -- | Update the element at @a@ to be @b@
  writeArray     :: SymWord b => array a b -> SBV a -> SBV b -> array a b
  -- | Merge two given arrays on the symbolic condition
  -- Intuitively: @mergeArrays cond a b = if cond then a else b@.
  -- Merging pushes the if-then-else choice down on to elements
  mergeArrays    :: SymWord b => SBV Bool -> array a b -> array a b -> array a b

-- | Arrays implemented in terms of SMT-arrays: <http://smtlib.cs.uiowa.edu/theories/ArraysEx.smt2>
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
  show (SArray{}) = "SArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

instance SymArray SArray where
  newArray_                                      = declNewSArray (\t -> "array_" ++ show t)
  newArray n                                     = declNewSArray (const n)
  readArray   (SArray arr) (SBV a)               = SBV (readSArr arr a)
  resetArray  (SArray arr) (SBV b)               = SArray (resetSArr arr b)
  writeArray  (SArray arr) (SBV a)    (SBV b)    = SArray (writeSArr arr a b)
  mergeArrays (SBV t)      (SArray a) (SArray b) = SArray (mergeSArr t a b)

-- | Declare a new symbolic array, with a potential initial value
declNewSArray :: forall a b. (HasKind a, HasKind b) => (Int -> String) -> Maybe (SBV b) -> Symbolic (SArray a b)
declNewSArray mkNm mbInit = do
   let aknd = kindOf (undefined :: a)
       bknd = kindOf (undefined :: b)
   arr <- newSArr (aknd, bknd) mkNm (fmap unSBV mbInit)
   return (SArray arr)

-- | Declare a new functional symbolic array, with a potential initial value. Note that a read from an uninitialized cell will result in an error.
declNewSFunArray :: forall a b. (HasKind a, HasKind b) => Maybe (SBV b) -> Symbolic (SFunArray a b)
declNewSFunArray mbiVal = return $ SFunArray $ const $ fromMaybe (error "Reading from an uninitialized array entry") mbiVal

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
data SFunArray a b = SFunArray (SBV a -> SBV b)

instance (HasKind a, HasKind b) => Show (SFunArray a b) where
  show (SFunArray _) = "SFunArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

-- | Lift a function to an array. Useful for creating arrays in a pure context. (Otherwise use `newArray`.)
mkSFunArray :: (SBV a -> SBV b) -> SFunArray a b
mkSFunArray = SFunArray

-- | Add a constraint with a given probability
addConstraint :: Maybe Double -> SBool -> SBool -> Symbolic ()
addConstraint mt (SBV c) (SBV c') = addSValConstraint mt c c'

instance NFData a => NFData (SBV a) where
  rnf (SBV x) = rnf x `seq` ()
