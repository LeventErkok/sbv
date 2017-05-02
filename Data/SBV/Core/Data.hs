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
 , Op(..), FPOp(..), NamedSymVar, getTableIndex
 , SBVPgm(..), Symbolic, SExecutable(..), runSymbolic, runSymbolic', State, getPathCondition, extendPathCondition
 , inProofMode, SBVRunMode(..), Kind(..), Outputtable(..), Result(..)
 , Logic(..), SMTLibLogic(..)
 , addConstraint, internalVariable, internalConstraint, isCodeGenMode
 , SBVType(..), newUninterpreted, addAxiom
 , Quantifier(..), needsExistentials
 , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension, smtLibReservedNames
 , SolverCapabilities(..)
 , extractSymbolicSimulationState
 , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..), getSBranchRunConfig
 , declNewSArray, declNewSFunArray
 , OptimizeStyle(..), Penalty(..), Objective(..)
 , Tactic(..), CaseCond(..), SMTProblem(..), isParallelCaseAnywhere
 ) where

import Control.DeepSeq      (NFData(..))
import Control.Monad.Reader (ask)
import Control.Monad.Trans  (liftIO)
import Data.Int             (Int8, Int16, Int32, Int64)
import Data.Word            (Word8, Word16, Word32, Word64)
import Data.List            (elemIndex, intercalate)
import Data.Maybe           (fromMaybe)

import qualified Data.Set as Set (Set)
import qualified Data.Generics as G    (Data(..))

import GHC.Stack.Compat
#if !MIN_VERSION_base(4,9,0)
import GHC.SrcLoc.Compat
#endif

import System.Random

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic

import Data.SBV.SMT.SMTLibNames

import Data.SBV.Utils.Lib

import Prelude ()
import Prelude.Compat

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
newtype SFunArray a b = SFunArray (SBV a -> SBV b)

instance (HasKind a, HasKind b) => Show (SFunArray a b) where
  show (SFunArray _) = "SFunArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

-- | Lift a function to an array. Useful for creating arrays in a pure context. (Otherwise use `newArray`.)
mkSFunArray :: (SBV a -> SBV b) -> SFunArray a b
mkSFunArray = SFunArray

-- | Add a constraint with a given probability.
addConstraint :: Maybe Double -> SBool -> SBool -> Symbolic ()
addConstraint mt (SBV c) (SBV c') = addSValConstraint mt c c'

-- | A case condition (internal)
data CaseCond = NoCase                         -- ^ No case-split
              | CasePath [SW]                  -- ^ In a case-path
              | CaseVac  [SW] SW               -- ^ For checking the vacuity of a case
              | CaseCov  [SW] [SW]             -- ^ In a case-path end, coverage (first arg is path cond, second arg is coverage cond)
              | CstrVac                        -- ^ In a constraint vacuity check (top-level)
              | Opt      [Objective (SW, SW)]  -- ^ In an optimization call

instance NFData CaseCond where
  rnf NoCase           = ()
  rnf (CasePath ps)    = rnf ps
  rnf (CaseVac  ps q)  = rnf ps `seq` rnf q  `seq` ()
  rnf (CaseCov  ps qs) = rnf ps `seq` rnf qs `seq` ()
  rnf CstrVac          = ()
  rnf (Opt os)         = rnf os `seq` ()

-- | Internal representation of a symbolic simulation result
data SMTProblem = SMTProblem { smtInputs    :: [(Quantifier, NamedSymVar)]        -- ^ inputs
                             , smtSkolemMap :: [Either SW (SW, [SW])]             -- ^ skolem-map
                             , kindsUsed    :: Set.Set Kind                       -- ^ kinds used
                             , smtAsserts   :: [(String, Maybe CallStack, SW)]    -- ^ assertions
                             , tactics      :: [Tactic SW]                        -- ^ tactics to use
                             , objectives   :: [Objective (SW, SW)]               -- ^ optimization goals, if any
                             , smtLibPgm    :: SMTConfig -> CaseCond -> SMTLibPgm -- ^ SMTLib representation, given the config and case-splits
                             }

instance NFData SMTProblem where
  rnf (SMTProblem i m k a t o p) = rnf i `seq` rnf m `seq` rnf k `seq` rnf a `seq` rnf t `seq` rnf o `seq` rnf p `seq` ()

instance NFData (SBV a) where
  rnf (SBV x) = rnf x `seq` ()

-- | Symbolically executable program fragments. This class is mainly used for 'safe' calls, and is sufficently populated internally to cover most use
-- cases. Users can extend it as they wish to allow 'safe' checks for SBV programs that return/take types that are user-defined.
class SExecutable a where
   sName_ :: a -> Symbolic ()
   sName  :: [String] -> a -> Symbolic ()

instance NFData a => SExecutable (Symbolic a) where
   sName_   a = a >>= \r -> rnf r `seq` return ()
   sName []   = sName_
   sName xs   = error $ "SBV.SExecutable.sName: Extra unmapped name(s): " ++ intercalate ", " xs

instance SExecutable (SBV a) where
   sName_   v = sName_ (output v)
   sName xs v = sName xs (output v)

-- Unit output
instance SExecutable () where
   sName_   () = sName_   (output ())
   sName xs () = sName xs (output ())

-- List output
instance SExecutable [SBV a] where
   sName_   vs = sName_   (output vs)
   sName xs vs = sName xs (output vs)

-- 2 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b) => SExecutable (SBV a, SBV b) where
  sName_ (a, b) = sName_ (output a >> output b)
  sName _       = sName_

-- 3 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c) => SExecutable (SBV a, SBV b, SBV c) where
  sName_ (a, b, c) = sName_ (output a >> output b >> output c)
  sName _          = sName_

-- 4 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d) => SExecutable (SBV a, SBV b, SBV c, SBV d) where
  sName_ (a, b, c, d) = sName_ (output a >> output b >> output c >> output c >> output d)
  sName _             = sName_

-- 5 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e) where
  sName_ (a, b, c, d, e) = sName_ (output a >> output b >> output c >> output d >> output e)
  sName _                = sName_

-- 6 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e, NFData f, SymWord f) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  sName_ (a, b, c, d, e, f) = sName_ (output a >> output b >> output c >> output d >> output e >> output f)
  sName _                   = sName_

-- 7 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e, NFData f, SymWord f, NFData g, SymWord g) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  sName_ (a, b, c, d, e, f, g) = sName_ (output a >> output b >> output c >> output d >> output e >> output f >> output g)
  sName _                      = sName_

-- Functions
instance (SymWord a, SExecutable p) => SExecutable (SBV a -> p) where
   sName_        k = forall_   >>= \a -> sName_   $ k a
   sName (s:ss)  k = forall s  >>= \a -> sName ss $ k a
   sName []      k = sName_ k

-- 2 Tuple input
instance (SymWord a, SymWord b, SExecutable p) => SExecutable ((SBV a, SBV b) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b -> k (a, b)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b -> k (a, b)
  sName []      k = sName_ k

-- 3 Tuple input
instance (SymWord a, SymWord b, SymWord c, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c) -> p) where
  sName_       k  = forall_  >>= \a -> sName_   $ \b c -> k (a, b, c)
  sName (s:ss) k  = forall s >>= \a -> sName ss $ \b c -> k (a, b, c)
  sName []     k  = sName_ k

-- 4 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d -> k (a, b, c, d)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d -> k (a, b, c, d)
  sName []      k = sName_ k

-- 5 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d e -> k (a, b, c, d, e)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d e -> k (a, b, c, d, e)
  sName []      k = sName_ k

-- 6 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d e f -> k (a, b, c, d, e, f)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d e f -> k (a, b, c, d, e, f)
  sName []      k = sName_ k

-- 7 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName []      k = sName_ k
