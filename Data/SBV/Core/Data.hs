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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}

module Data.SBV.Core.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64, SInteger, SReal, SFloat, SDouble, SChar, SString, SList
 , nan, infinity, sNaN, sInfinity, RoundingMode(..), SRoundingMode
 , sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive, sRoundTowardNegative, sRoundTowardZero
 , sRNE, sRNA, sRTP, sRTN, sRTZ
 , SymWord(..)
 , CW(..), CWVal(..), AlgReal(..), AlgRealPoly, ExtCW(..), GeneralizedCW(..), isRegularCW, cwSameType, cwToBool
 , mkConstCW ,liftCW2, mapCW, mapCW2
 , SW(..), trueSW, falseSW, trueCW, falseCW, normCW
 , SVal(..)
 , SBV(..), NodeId(..), mkSymSBV
 , ArrayContext(..), ArrayInfo, SymArray(..), SFunArray(..), SArray(..)
 , sbvToSW, sbvToSymSW, forceSWArg
 , SBVExpr(..), newExpr
 , cache, Cached, uncache, uncacheAI, HasKind(..)
 , Op(..), PBOp(..), FPOp(..), StrOp(..), SeqOp(..), RegExp(..), NamedSymVar, getTableIndex
 , SBVPgm(..), Symbolic, runSymbolic, State, getPathCondition, extendPathCondition
 , inSMTMode, SBVRunMode(..), Kind(..), Outputtable(..), Result(..)
 , SolverContext(..), internalVariable, internalConstraint, isCodeGenMode
 , SBVType(..), newUninterpreted, addAxiom
 , Quantifier(..), needsExistentials
 , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension, smtLibReservedNames
 , SolverCapabilities(..)
 , extractSymbolicSimulationState
 , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..)
 , OptimizeStyle(..), Penalty(..), Objective(..)
 , QueryState(..), Query(..), SMTProblem(..)
 ) where

import GHC.Generics (Generic)
import GHC.Exts     (IsList(..))

import Control.DeepSeq      (NFData(..))
import Control.Monad.Reader (ask)
import Control.Monad.Trans  (liftIO)
import Data.Int             (Int8, Int16, Int32, Int64)
import Data.Word            (Word8, Word16, Word32, Word64)
import Data.List            (elemIndex)
import Data.Maybe           (fromMaybe)
import Data.Typeable        (Typeable)

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

-- | A symbolic character. Note that, as far as SBV's symbolic strings are concerned, a character
-- is currently an 8-bit unsigned value, corresponding to the ISO-8859-1 (Latin-1) character
-- set: <http://en.wikipedia.org/wiki/ISO/IEC_8859-1>. A Haskell 'Char', on the other hand, is based
-- on unicode. Therefore, there isn't a 1-1 correspondence between a Haskell character and an SBV
-- character for the time being. This limitation is due to the SMT-solvers only supporting this
-- particular subset. However, there is a pending proposal to add support for unicode, and SBV
-- will track these changes to have full unicode support as solvers become available. For
-- details, see: <http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>
type SChar = SBV Char

-- | A symbolic string. Note that a symbolic string is /not/ a list of symbolic characters,
-- that is, it is not the case that @SString = [SChar]@, unlike what one might expect following
-- Haskell strings. An 'SString' is a symbolic value of its own, of possibly arbitrary but finite length,
-- and internally processed as one unit as opposed to a fixed-length list of characters.
type SString = SBV String

-- | A symbolic list of items. Note that a symbolic list is /not/ a list of symbolic items,
-- that is, it is not the case that @SList a = [a]@, unlike what one might expect following
-- haskell lists\/sequences. An 'SList' is a symbolic value of its own, of possibly arbitrary but finite
-- length, and internally processed as one unit as opposed to a fixed-length list of items.
-- Note that lists can be nested, i.e., we do allow lists of lists of ... items.
type SList a = SBV [a]

-- | IsList instance allows list literals to be written compactly.
instance SymWord [a] => IsList (SList a) where
  type Item (SList a) = a
  fromList = literal
  toList x = fromMaybe (error "IsList.toList used in a symbolic context!") (unliteral x)

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

-- | Internal representation of a symbolic simulation result
newtype SMTProblem = SMTProblem {smtLibPgm :: SMTConfig -> SMTLibPgm} -- ^ SMTLib representation, given the config

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

-- | A 'Show' instance is not particularly "desirable," when the value is symbolic,
-- but we do need this instance as otherwise we cannot simply evaluate Haskell functions 
-- that return symbolic values and have their constant values printed easily!
instance Show (SBV a) where
  show (SBV sv) = show sv

-- | Equality constraint on SBV values. Not desirable since we can't really compare two
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
   -- | Add a soft constraint. The solver will try to satisfy this condition if possible, but won't if it cannot
   softConstrain   :: SBool -> m ()
   -- | Add a named constraint. The name is used in unsat-core extraction.
   namedConstraint :: String -> SBool -> m ()
   -- | Add a constraint, with arbitrary attributes. Used in interpolant generation.
   constrainWithAttribute :: [(String, String)] -> SBool -> m ()
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
class (HasKind a, Ord a, Typeable a) => SymWord a where
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
-- If a default value is supplied, then all the array elements will be initialized to this value.
-- Otherwise, they will be left unspecified, i.e., a read from an unwritten location will produce
-- an uninterpreted constant.
--
-- While it's certainly possible for user to create instances of 'SymArray', the
-- 'SArray' and 'SFunArray' instances already provided should cover most use cases
-- in practice. Note that there are a few differences between these two models in
-- terms of use models:
--
--    * 'SArray' produces SMTLib arrays, and requires a solver that understands the
--      array theory. 'SFunArray' is internally handled, and thus can be used with
--      any solver. (Note that all solvers except 'abc' support arrays, so this isn't
--      a big decision factor.)
--
--    * For both arrays, if a default value is supplied, then reading from uninitialized
--      cell will return that value. If the default is not given, then reading from
--      uninitialized cells is still OK for both arrays, and will produce an uninterpreted
--      constant in both cases.
--
--    * Only 'SArray' supports checking equality of arrays. (That is, checking if an entire
--      array is equivalent to another.) 'SFunArray's cannot be checked for equality. In general,
--      checking wholesale equality of arrays is a difficult decision problem and should be
--      avoided if possible.
--
--    * Only 'SFunArray' supports compilation to C. Programs using 'SArray' will not be
--      accepted by the C-code generator.
--
--    * You cannot use quickcheck on programs that contain these arrays. (Neither 'SArray'
--      nor 'SFunArray'.)
--
--    * With 'SArray', SBV transfers all array-processing to the SMT-solver. So, it can generate
--      programs more quickly, but they might end up being too hard for the solver to handle. With
--      'SFunArray', SBV only generates code for individual elements and the array itself never
--      shows up in the resulting SMTLib program. This puts more onus on the SBV side and might
--      have some performance impacts, but it might generate problems that are easier for the SMT
--      solvers to handle. 
--
-- As a rule of thumb, try 'SArray' first. These should generate compact code. However, if
-- the backend solver has hard time solving the generated problems, switch to
-- 'SFunArray'. If you still have issues, please report so we can see what the problem might be!
class SymArray array where
  -- | Create a new anonymous array, possibly with a default initial value.
  newArray_      :: (HasKind a, HasKind b) => Maybe (SBV b) -> Symbolic (array a b)
  -- | Create a named new array, possibly with a default initial value.
  newArray       :: (HasKind a, HasKind b) => String -> Maybe (SBV b) -> Symbolic (array a b)
  -- | Read the array element at @a@
  readArray      :: array a b -> SBV a -> SBV b
  -- | Update the element at @a@ to be @b@
  writeArray     :: SymWord b => array a b -> SBV a -> SBV b -> array a b
  -- | Merge two given arrays on the symbolic condition
  -- Intuitively: @mergeArrays cond a b = if cond then a else b@.
  -- Merging pushes the if-then-else choice down on to elements
  mergeArrays    :: SymWord b => SBV Bool -> array a b -> array a b -> array a b
  -- | Internal function, not exported to the user
  newArrayInState :: (HasKind a, HasKind b) => Maybe String -> Maybe (SBV b) -> State -> IO (array a b)

  {-# MINIMAL readArray, writeArray, mergeArrays, newArrayInState #-}
  newArray_   mbVal = ask >>= liftIO . newArrayInState Nothing   mbVal
  newArray nm mbVal = ask >>= liftIO . newArrayInState (Just nm) mbVal

-- | Arrays implemented in terms of SMT-arrays: <http://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml>
--
--   * Maps directly to SMT-lib arrays
--
--   * Reading from an unintialized value is OK. If the default value is given in 'newArray', it will
--     be the result. Otherwise, the read yields an uninterpreted constant.
--
--   * Can check for equality of these arrays
--
--   * Cannot be used in code-generation (i.e., compilation to C)
--
--   * Cannot quick-check theorems using @SArray@ values
--
--   * Typically slower as it heavily relies on SMT-solving for the array theory
newtype SArray a b = SArray { unSArray :: SArr }

instance (HasKind a, HasKind b) => Show (SArray a b) where
  show SArray{} = "SArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

instance SymArray SArray where
  readArray   (SArray arr) (SBV a)               = SBV (readSArr arr a)
  writeArray  (SArray arr) (SBV a)    (SBV b)    = SArray (writeSArr arr a b)
  mergeArrays (SBV t)      (SArray a) (SArray b) = SArray (mergeSArr t a b)

  newArrayInState :: forall a b. (HasKind a, HasKind b) => Maybe String -> Maybe (SBV b) -> State -> IO (SArray a b)
  newArrayInState mbNm mbVal st = do mapM_ (registerKind st) [aknd, bknd]
                                     SArray <$> newSArr st (aknd, bknd) (mkNm mbNm) (unSBV <$> mbVal)
     where mkNm Nothing   t = "array_" ++ show t
           mkNm (Just nm) _ = nm
           aknd = kindOf (undefined :: a)
           bknd = kindOf (undefined :: b)

-- | Arrays implemented internally, without translating to SMT-Lib functions:
--
--   * Internally handled by the library and not mapped to SMT-Lib, hence can
--     be used with solvers that don't support arrays. (Such as abc.)
--
--   * Reading from an unintialized value is OK. If the default value is given in 'newArray', it will
--     be the result. Otherwise, the read yields an uninterpreted constant.
--
--   * Cannot check for equality of arrays.
--
--   * Can be used in code-generation (i.e., compilation to C).
--
--   * Can not quick-check theorems using @SFunArray@ values
--
--   * Typically faster as it gets compiled away during translation.
newtype SFunArray a b = SFunArray { unSFunArray :: SFunArr }

instance (HasKind a, HasKind b) => Show (SFunArray a b) where
  show SFunArray{} = "SFunArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

instance SymArray SFunArray where
  readArray   (SFunArray arr) (SBV a)             = SBV (readSFunArr arr a)
  writeArray  (SFunArray arr) (SBV a) (SBV b)     = SFunArray (writeSFunArr arr a b)
  mergeArrays (SBV t) (SFunArray a) (SFunArray b) = SFunArray (mergeSFunArr t a b)

  newArrayInState :: forall a b. (HasKind a, HasKind b) => Maybe String -> Maybe (SBV b) -> State -> IO (SFunArray a b)
  newArrayInState mbNm mbVal st = do mapM_ (registerKind st) [aknd, bknd]
                                     SFunArray <$> newSFunArr st (aknd, bknd) (mkNm mbNm) (unSBV <$> mbVal)
    where mkNm Nothing t   = "funArray_" ++ show t
          mkNm (Just nm) _ = nm
          aknd = kindOf (undefined :: a)
          bknd = kindOf (undefined :: b)
