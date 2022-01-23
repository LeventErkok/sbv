-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Data
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64, SInteger, SReal, SFloat, SDouble
 , SFloatingPoint, SFPHalf, SFPBFloat, SFPSingle, SFPDouble, SFPQuad
 , SRational
 , SChar, SString, SList
 , SEither, SMaybe
 , STuple, STuple2, STuple3, STuple4, STuple5, STuple6, STuple7, STuple8
 , RCSet(..), SSet
 , nan, infinity, sNaN, sInfinity, RoundingMode(..), SRoundingMode
 , sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive, sRoundTowardNegative, sRoundTowardZero
 , sRNE, sRNA, sRTP, sRTN, sRTZ
 , SymVal(..)
 , CV(..), CVal(..), AlgReal(..), AlgRealPoly(..), ExtCV(..), GeneralizedCV(..), isRegularCV, cvSameType, cvToBool
 , mkConstCV ,liftCV2, mapCV, mapCV2
 , SV(..), trueSV, falseSV, trueCV, falseCV, normCV
 , SVal(..)
 , sTrue, sFalse, sNot, (.&&), (.||), (.<+>), (.~&), (.~|), (.=>), (.<=>), sAnd, sOr, sAny, sAll, fromBool
 , SBV(..), NodeId(..), mkSymSBV
 , ArrayContext(..), ArrayInfo, SymArray(..), SArray(..)
 , sbvToSV, sbvToSymSV, forceSVArg
 , SBVExpr(..), newExpr
 , cache, Cached, uncache, uncacheAI, HasKind(..)
 , Op(..), PBOp(..), FPOp(..), StrOp(..), RegExOp(..), SeqOp(..), RegExp(..), NamedSymVar(..), getTableIndex
 , SBVPgm(..), Symbolic, runSymbolic, State, getPathCondition, extendPathCondition
 , inSMTMode, SBVRunMode(..), Kind(..), Outputtable(..), Result(..)
 , SolverContext(..), internalVariable, internalConstraint, isCodeGenMode
 , SBVType(..), newUninterpreted
 , Quantifier(..), needsExistentials
 , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension, smtLibReservedNames
 , SolverCapabilities(..)
 , extractSymbolicSimulationState
 , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..)
 , OptimizeStyle(..), Penalty(..), Objective(..)
 , QueryState(..), QueryT(..), SMTProblem(..)
 ) where

import GHC.TypeLits

import GHC.Generics (Generic)
import GHC.Exts     (IsList(..))

import Control.DeepSeq        (NFData(..))
import Control.Monad.Trans    (liftIO)
import Data.Int               (Int8, Int16, Int32, Int64)
import Data.Word              (Word8, Word16, Word32, Word64)
import Data.List              (elemIndex)
import Data.Maybe             (fromMaybe)

import Data.Proxy
import Data.Typeable          (Typeable)

import qualified Data.Generics as G    (Data(..))

import qualified Data.IORef         as R    (readIORef)
import qualified Data.IntMap.Strict as IMap (size, insert)

import System.Random

import Data.SBV.Core.AlgReals
import Data.SBV.Core.SizedFloats
import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Operations

import Data.SBV.Control.Types

import Data.SBV.SMT.SMTLibNames

import Data.SBV.Utils.Lib

-- | Get the current path condition
getPathCondition :: State -> SBool
getPathCondition st = SBV (getSValPathCondition st)

-- | Extend the path condition with the given test value.
extendPathCondition :: State -> (SBool -> SBool) -> State
extendPathCondition st f = extendSValPathCondition st (unSBV . f . SBV)

-- | The "Symbolic" value. The parameter @a@ is phantom, but is
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

-- | A symbolic arbitrary precision floating point value
type SFloatingPoint (eb :: Nat) (sb :: Nat) = SBV (FloatingPoint eb sb)

-- | A symbolic half-precision float
type SFPHalf = SBV FPHalf

-- | A symbolic brain-float precision float
type SFPBFloat = SBV FPBFloat

-- | A symbolic single-precision float
type SFPSingle = SBV FPSingle

-- | A symbolic double-precision float
type SFPDouble = SBV FPDouble

-- | A symbolic quad-precision float
type SFPQuad = SBV FPQuad

-- | A symbolic character. Note that this is the full unicode character set.
-- see: <http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>
-- for details.
type SChar = SBV Char

-- | A symbolic string. Note that a symbolic string is /not/ a list of symbolic characters,
-- that is, it is not the case that @SString = [SChar]@, unlike what one might expect following
-- Haskell strings. An 'SString' is a symbolic value of its own, of possibly arbitrary but finite length,
-- and internally processed as one unit as opposed to a fixed-length list of characters.
type SString = SBV String

-- | A symbolic rational value.
type SRational = SBV Rational

-- | A symbolic list of items. Note that a symbolic list is /not/ a list of symbolic items,
-- that is, it is not the case that @SList a = [a]@, unlike what one might expect following
-- haskell lists\/sequences. An 'SList' is a symbolic value of its own, of possibly arbitrary but finite
-- length, and internally processed as one unit as opposed to a fixed-length list of items.
-- Note that lists can be nested, i.e., we do allow lists of lists of ... items.
type SList a = SBV [a]

-- | Symbolic 'Either'
type SEither a b = SBV (Either a b)

-- | Symbolic 'Maybe'
type SMaybe a = SBV (Maybe a)

-- | Symbolic 'Data.Set'. Note that we use 'RCSet', which supports
-- both regular sets and complements, i.e., those obtained from the
-- universal set (of the right type) by removing elements.
type SSet a = SBV (RCSet a)

-- | Symbolic 2-tuple. NB. 'STuple' and 'STuple2' are equivalent.
type STuple a b = SBV (a, b)

-- | Symbolic 2-tuple. NB. 'STuple' and 'STuple2' are equivalent.
type STuple2 a b = SBV (a, b)

-- | Symbolic 3-tuple.
type STuple3 a b c = SBV (a, b, c)

-- | Symbolic 4-tuple.
type STuple4 a b c d = SBV (a, b, c, d)

-- | Symbolic 5-tuple.
type STuple5 a b c d e = SBV (a, b, c, d, e)

-- | Symbolic 6-tuple.
type STuple6 a b c d e f = SBV (a, b, c, d, e, f)

-- | Symbolic 7-tuple.
type STuple7 a b c d e f g = SBV (a, b, c, d, e, f, g)

-- | Symbolic 8-tuple.
type STuple8 a b c d e f g h = SBV (a, b, c, d, e, f, g, h)

-- | IsList instance allows list literals to be written compactly.
instance SymVal [a] => IsList (SList a) where
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

-- | Symbolic variant of Not-A-Number. This value will inhabit
-- 'SFloat', 'SDouble' and 'SFloatingPoint'. types.
sNaN :: (Floating a, SymVal a) => SBV a
sNaN = literal nan

-- | Symbolic variant of infinity. This value will inhabit both
-- 'SFloat', 'SDouble' and 'SFloatingPoint'. types.
sInfinity :: (Floating a, SymVal a) => SBV a
sInfinity = literal infinity

-- | Internal representation of a symbolic simulation result
newtype SMTProblem = SMTProblem {smtLibPgm :: SMTConfig -> SMTLibPgm} -- ^ SMTLib representation, given the config

-- | Symbolic 'True'
sTrue :: SBool
sTrue = SBV (svBool True)

-- | Symbolic 'False'
sFalse :: SBool
sFalse = SBV (svBool False)

-- | Symbolic boolean negation
sNot :: SBool -> SBool
sNot (SBV b) = SBV (svNot b)

-- | Symbolic conjunction
infixr 3 .&&
(.&&) :: SBool -> SBool -> SBool
SBV x .&& SBV y = SBV (x `svAnd` y)

-- | Symbolic disjunction
infixr 2 .||
(.||) :: SBool -> SBool -> SBool
SBV x .|| SBV y = SBV (x `svOr` y)

-- | Symbolic logical xor
infixl 6 .<+>
(.<+>) :: SBool -> SBool -> SBool
SBV x .<+> SBV y = SBV (x `svXOr` y)

-- | Symbolic nand
infixr 3 .~&
(.~&) :: SBool -> SBool -> SBool
x .~& y = sNot (x .&& y)

-- | Symbolic nor
infixr 2 .~|
(.~|) :: SBool -> SBool -> SBool
x .~| y = sNot (x .|| y)

-- | Symbolic implication
infixr 1 .=>
(.=>) :: SBool -> SBool -> SBool
x .=> y = sNot x .|| y
-- NB. Do *not* try to optimize @x .=> x = True@ here! If constants go through, it'll get simplified.
-- The case "x .=> x" can hit is extremely rare, and the getAllSatResult function relies on this
-- trick to generate constraints in the unlucky case of ui-function models.

-- | Symbolic boolean equivalence
infixr 1 .<=>
(.<=>) :: SBool -> SBool -> SBool
x .<=> y = (x .&& y) .|| (sNot x .&& sNot y)

-- | Conversion from 'Bool' to 'SBool'
fromBool :: Bool -> SBool
fromBool True  = sTrue
fromBool False = sFalse

-- | Generalization of 'and'
sAnd :: [SBool] -> SBool
sAnd = foldr (.&&) sTrue

-- | Generalization of 'or'
sOr :: [SBool] -> SBool
sOr  = foldr (.||) sFalse

-- | Generalization of 'any'
sAny :: (a -> SBool) -> [a] -> SBool
sAny f = sOr  . map f

-- | Generalization of 'all'
sAll :: (a -> SBool) -> [a] -> SBool
sAll f = sAnd . map f

-- | 'RoundingMode' can be used symbolically
instance SymVal RoundingMode

-- | The symbolic variant of 'RoundingMode'
type SRoundingMode = SBV RoundingMode

-- | Symbolic variant of 'RoundNearestTiesToEven'
sRoundNearestTiesToEven :: SRoundingMode
sRoundNearestTiesToEven = literal RoundNearestTiesToEven

-- | Symbolic variant of 'RoundNearestTiesToAway'
sRoundNearestTiesToAway :: SRoundingMode
sRoundNearestTiesToAway = literal RoundNearestTiesToAway

-- | Symbolic variant of 'RoundTowardPositive'
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

-- | This instance is only defined so that we can define an instance for
-- 'Data.Bits.Bits'. '==' and '/=' simply throw an error. Use
-- 'Data.SBV.EqSymbolic' instead.
instance Eq (SBV a) where
  SBV a == SBV b = a == b
  SBV a /= SBV b = a /= b

instance HasKind a => HasKind (SBV a) where
  kindOf _ = kindOf (Proxy @a)

-- | Convert a symbolic value to a symbolic-word
sbvToSV :: State -> SBV a -> IO SV
sbvToSV st (SBV s) = svToSV st s

-------------------------------------------------------------------------
-- * Symbolic Computations
-------------------------------------------------------------------------

-- | Generalization of 'Data.SBV.mkSymSBV'
mkSymSBV :: forall a m. MonadSymbolic m => VarContext -> Kind -> Maybe String -> m (SBV a)
mkSymSBV vc k mbNm = SBV <$> (symbolicEnv >>= liftIO . svMkSymVar vc k mbNm)

-- | Generalization of 'Data.SBV.sbvToSymSW'
sbvToSymSV :: MonadSymbolic m => SBV a -> m SV
sbvToSymSV sbv = do
        st <- symbolicEnv
        liftIO $ sbvToSV st sbv

-- | Actions we can do in a context: Either at problem description
-- time or while we are dynamically querying. 'Symbolic' and 'Query' are
-- two instances of this class. Note that we use this mechanism
-- internally and do not export it from SBV.
class SolverContext m where
   -- | Add a constraint, any satisfying instance must satisfy this condition.
   constrain :: SBool -> m ()
   -- | Add a soft constraint. The solver will try to satisfy this condition if possible, but won't if it cannot.
   softConstrain :: SBool -> m ()
   -- | Add a named constraint. The name is used in unsat-core extraction.
   namedConstraint :: String -> SBool -> m ()
   -- | Add a constraint, with arbitrary attributes.
   constrainWithAttribute :: [(String, String)] -> SBool -> m ()
   -- | Set info. Example: @setInfo ":status" ["unsat"]@.
   setInfo :: String -> [String] -> m ()
   -- | Set an option.
   setOption :: SMTOption -> m ()
   -- | Set the logic.
   setLogic :: Logic -> m ()
   -- | Add a user specified axiom to the generated SMT-Lib file. The first argument is a mere
   -- string, use for commenting purposes. The second argument is intended to hold the multiple-lines
   -- of the axiom text as expressed in SMT-Lib notation. Note that we perform no checks on the axiom
   -- itself, to see whether it's actually well-formed or is sensible by any means.
   -- A separate formalization of SMT-Lib would be very useful here.
   addAxiom :: String -> [String] -> m ()
   -- | Add a user-defined SMTLib function. You should define the name given here as an uninterpreted
   -- value as well. SBV performs no checks on the SMTLib definition you give, so if it doesn't match
   -- the required type, or is malformed in any way, the call will fail at run-time.
   addSMTDefinition :: String -> [String] -> m ()
   -- | Set a solver time-out value, in milli-seconds. This function
   -- essentially translates to the SMTLib call @(set-info :timeout val)@,
   -- and your backend solver may or may not support it! The amount given
   -- is in milliseconds. Also see the function 'Data.SBV.Control.timeOut' for finer level
   -- control of time-outs, directly from SBV.
   setTimeOut :: Integer -> m ()
   -- | Get the state associated with this context
   contextState :: m State

   {-# MINIMAL constrain, softConstrain, namedConstraint, constrainWithAttribute, setOption, addAxiom, addSMTDefinition, contextState #-}

   -- time-out, logic, and info are  simply options in our implementation, so default implementation suffices
   setTimeOut t = setOption $ OptionKeyword ":timeout" [show t]
   setLogic     = setOption . SetLogic
   setInfo    k = setOption . SetInfo k

-- | A class representing what can be returned from a symbolic computation.
class Outputtable a where
  -- | Generalization of 'Data.SBV.output'
  output :: MonadSymbolic m => a -> m a

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
-- * Symbolic Values
-------------------------------------------------------------------------------
-- | A 'SymVal' is a potential symbolic value that can be created instances of to be fed to a symbolic program.
class (HasKind a, Typeable a) => SymVal a where
  -- | Generalization of 'Data.SBV.mkSymVal'
  mkSymVal :: MonadSymbolic m => VarContext -> Maybe String -> m (SBV a)
  -- | Turn a literal constant to symbolic
  literal :: a -> SBV a
  -- | Extract a literal, from a CV representation
  fromCV :: CV -> a
  -- | Does it concretely satisfy the given predicate?
  isConcretely :: SBV a -> (a -> Bool) -> Bool

  -- minimal complete definition: Nothing.
  -- Giving no instances is okay when defining an uninterpreted/enumerated sort, but otherwise you really
  -- want to define: literal, fromCV, mkSymVal

  default mkSymVal :: (MonadSymbolic m, Read a, G.Data a) => VarContext -> Maybe String -> m (SBV a)
  mkSymVal vc mbNm = SBV <$> (symbolicEnv >>= liftIO . svMkSymVar vc k mbNm)
    where -- NB.A call of the form
          --      constructUKind (Proxy @a)
          -- would be wrong here, as it would uninterpret the Proxy datatype!
          -- So, we have to use the dreaded undefined value in this case.
          k = constructUKind (undefined :: a)

  default literal :: Show a => a -> SBV a
  literal x = let k  = kindOf x
                  sx = show x
                  conts = case k of
                           KUserSort _ cts -> cts
                           _               -> Nothing
                  mbIdx = case conts of
                            Just xs -> sx `elemIndex` xs
                            Nothing -> Nothing
              in SBV $ SVal k (Left (CV k (CUserSort (mbIdx, sx))))

  default fromCV :: Read a => CV -> a
  fromCV (CV _ (CUserSort (_, s))) = read s
  fromCV cv                        = error $ "Cannot convert CV " ++ show cv ++ " to kind " ++ show (kindOf (Proxy @a))

  isConcretely s p
    | Just i <- unliteral s = p i
    | True                  = False

  -- | Generalization of 'Data.SBV.sbvForall'
  sbvForall :: MonadSymbolic m => String -> m (SBV a)
  sbvForall = mkSymVal (NonQueryVar (Just ALL)) . Just

  -- | Generalization of 'Data.SBV.sbvForall_'
  sbvForall_ :: MonadSymbolic m => m (SBV a)
  sbvForall_ = mkSymVal (NonQueryVar (Just ALL)) Nothing

  -- | Generalization of 'Data.SBV.mkForallVars'
  mkForallVars :: MonadSymbolic m => Int -> m [SBV a]
  mkForallVars n = mapM (const sbvForall_) [1 .. n]

  -- | Generalization of 'Data.SBV.sbvExists'
  sbvExists :: MonadSymbolic m => String -> m (SBV a)
  sbvExists = mkSymVal (NonQueryVar (Just EX)) . Just

  -- | Generalization of 'Data.SBV.sbvExists_'
  sbvExists_ :: MonadSymbolic m => m (SBV a)
  sbvExists_ = mkSymVal (NonQueryVar (Just EX)) Nothing

  -- | Generalization of 'Data.SBV.mkExistVars'
  mkExistVars :: MonadSymbolic m => Int -> m [SBV a]
  mkExistVars n = mapM (const sbvExists_) [1 .. n]

  -- | Generalization of 'Data.SBV.free'
  free :: MonadSymbolic m => String -> m (SBV a)
  free = mkSymVal (NonQueryVar Nothing) . Just

  -- | Generalization of 'Data.SBV.free_'
  free_ :: MonadSymbolic m => m (SBV a)
  free_ = mkSymVal (NonQueryVar Nothing) Nothing

  -- | Generalization of 'Data.SBV.mkFreeVars'
  mkFreeVars :: MonadSymbolic m => Int -> m [SBV a]
  mkFreeVars n = mapM (const free_) [1 .. n]

  -- | Generalization of 'Data.SBV.symbolic'
  symbolic :: MonadSymbolic m => String -> m (SBV a)
  symbolic = free

  -- | Generalization of 'Data.SBV.symbolics'
  symbolics :: MonadSymbolic m => [String] -> m [SBV a]
  symbolics = mapM symbolic

  -- | Extract a literal, if the value is concrete
  unliteral :: SBV a -> Maybe a
  unliteral (SBV (SVal _ (Left c))) = Just $ fromCV c
  unliteral _                       = Nothing

  -- | Is the symbolic word concrete?
  isConcrete :: SBV a -> Bool
  isConcrete (SBV (SVal _ (Left _))) = True
  isConcrete _                       = False

  -- | Is the symbolic word really symbolic?
  isSymbolic :: SBV a -> Bool
  isSymbolic = not . isConcrete

instance (Random a, SymVal a) => Random (SBV a) where
  randomR (l, h) g = case (unliteral l, unliteral h) of
                       (Just lb, Just hb) -> let (v, g') = randomR (lb, hb) g in (literal (v :: a), g')
                       _                  -> error "SBV.Random: Cannot generate random values with symbolic bounds"
  random         g = let (v, g') = random g in (literal (v :: a) , g')

---------------------------------------------------------------------------------
-- * Symbolic Arrays
---------------------------------------------------------------------------------

-- | Arrays of symbolic values
-- An @array a b@ is an array indexed by the type @'SBV' a@, with elements of type @'SBV' b@.
--
-- If a default value is supplied, then all the array elements will be initialized to this value.
-- Otherwise, they will be left unspecified, i.e., a read from an unwritten location will produce
-- an uninterpreted constant.
--
-- The reason for this class is rather historic. In the past, SBV provided two different kinds of
-- arrays: an `SArray` abstraction that mapped directly to SMTLib arrays  (which is still available
-- today), and a functional notion of arrays that used internal caching, called @SFunArray@. The latter
-- has been removed as the code turned out to be rather tricky and hard to maintain; so we only
-- have one instance of this class. But end users can add their own instances, if needed.
--
-- NB. 'sListArray' insists on a concrete initializer, because not having one would break
-- referential transparency. See https://github.com/LeventErkok/sbv/issues/553 for details.
class SymArray array where
  -- | Generalization of 'Data.SBV.newArray_'
  newArray_      :: (MonadSymbolic m, HasKind a, HasKind b) => Maybe (SBV b) -> m (array a b)
  -- | Generalization of 'Data.SBV.newArray'
  newArray       :: (MonadSymbolic m, HasKind a, HasKind b) => String -> Maybe (SBV b) -> m (array a b)
  -- | Create a literal array
  sListArray     :: (HasKind a, SymVal b) => b -> [(SBV a, SBV b)] -> array a b
  -- | Read the array element at @a@
  readArray      :: array a b -> SBV a -> SBV b
  -- | Update the element at @a@ to be @b@
  writeArray     :: SymVal b => array a b -> SBV a -> SBV b -> array a b
  -- | Merge two given arrays on the symbolic condition
  -- Intuitively: @mergeArrays cond a b = if cond then a else b@.
  -- Merging pushes the if-then-else choice down on to elements
  mergeArrays    :: SymVal b => SBV Bool -> array a b -> array a b -> array a b
  -- | Internal function, not exported to the user
  newArrayInState :: (HasKind a, HasKind b) => Maybe String -> Maybe (SBV b) -> State -> IO (array a b)

  {-# MINIMAL readArray, writeArray, mergeArrays, ((newArray_, newArray) | newArrayInState), sListArray #-}
  newArray_   mbVal = symbolicEnv >>= liftIO . newArrayInState Nothing   mbVal
  newArray nm mbVal = symbolicEnv >>= liftIO . newArrayInState (Just nm) mbVal

  -- Despite our MINIMAL pragma and default implementations for newArray_ and
  -- newArray, we must provide a dummy implementation for newArrayInState:
  newArrayInState = error "undefined: newArrayInState"

-- | Arrays implemented in terms of SMT-arrays: <http://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml>
--
--   * Maps directly to SMT-lib arrays
--
--   * Reading from an uninitialized value is OK. If the default value is given in 'newArray', it will
--     be the result. Otherwise, the read yields an uninterpreted constant.
--
--   * Can check for equality of these arrays
--
--   * Cannot be used in code-generation (i.e., compilation to C)
--
--   * Cannot quick-check theorems using @SArray@ values
newtype SArray a b = SArray { unSArray :: SArr }

instance (HasKind a, HasKind b) => Show (SArray a b) where
  show SArray{} = "SArray<" ++ showType (Proxy @a) ++ ":" ++ showType (Proxy @b) ++ ">"

instance SymArray SArray where
  readArray   (SArray arr) (SBV a)               = SBV (readSArr arr a)
  writeArray  (SArray arr) (SBV a)    (SBV b)    = SArray (writeSArr arr a b)
  mergeArrays (SBV t)      (SArray a) (SArray b) = SArray (mergeSArr t a b)

  sListArray :: forall a b. (HasKind a, SymVal b) => b -> [(SBV a, SBV b)] -> SArray a b
  sListArray initializer = foldl (uncurry . writeArray) arr
    where arr = SArray $ SArr ks $ cache r
           where ks   = (kindOf (Proxy @a), kindOf (Proxy @b))
                 r st = do amap <- R.readIORef (rArrayMap st)

                           let k    = ArrayIndex $ IMap.size amap
                               iVal = literal initializer

                           iSV <- sbvToSV st iVal

                           let upd  = IMap.insert (unArrayIndex k) ("array_" ++ show k, ks, ArrayFree (Just iSV))

                           k `seq` modifyState st rArrayMap upd $ modifyIncState st rNewArrs upd
                           return k

  newArrayInState :: forall a b. (HasKind a, HasKind b) => Maybe String -> Maybe (SBV b) -> State -> IO (SArray a b)
  newArrayInState mbNm mbVal st = do mapM_ (registerKind st) [aknd, bknd]
                                     SArray <$> newSArr st (aknd, bknd) (mkNm mbNm) (unSBV <$> mbVal)
     where mkNm Nothing   t = "array_" ++ show t
           mkNm (Just nm) _ = nm
           aknd = kindOf (Proxy @a)
           bknd = kindOf (Proxy @b)
