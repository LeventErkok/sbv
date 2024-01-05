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
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

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
 , Op(..), PBOp(..), FPOp(..), StrOp(..), RegExOp(..), SeqOp(..), RegExp(..), NamedSymVar(..), OvOp(..), getTableIndex
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
 , QueryState(..), QueryT(..), SMTProblem(..), Constraint(..), Lambda(..), Forall(..), Exists(..), ExistsUnique(..), ForallN(..), ExistsN(..)
 , QuantifiedBool(..), EqSymbolic(..), QNot(..), Skolemize(skolemize, taggedSkolemize)
 ) where

import GHC.TypeLits (KnownNat, Nat, Symbol, KnownSymbol, symbolVal, AppendSymbol)

import GHC.Exts     (IsList(..))

import Control.DeepSeq        (NFData(..))
import Control.Monad          (void, replicateM)
import Control.Monad.Trans    (liftIO, MonadIO)
import Data.Int               (Int8, Int16, Int32, Int64)
import Data.Word              (Word8, Word16, Word32, Word64)
import Data.List              (elemIndex)
import Data.Maybe             (fromMaybe)

import Data.Kind (Type)
import Data.Proxy
import Data.Typeable          (Typeable)

import GHC.Generics (Generic, U1(..), M1(..), (:*:)(..), K1(..), (:+:)(..))
import qualified GHC.Generics  as G
import qualified Data.Generics as G (Data(..))

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
SBV x .=> SBV y = SBV (x `svImplies` y)
-- NB. Do *not* try to optimize @x .=> x = True@ here! If constants go through, it'll get simplified.
-- The case "x .=> x" can hit is extremely rare, and the getAllSatResult function relies on this
-- trick to generate constraints in the unlucky case of ui-function models.

-- | Symbolic boolean equivalence
infixr 1 .<=>
(.<=>) :: SBool -> SBool -> SBool
SBV x .<=> SBV y = SBV (x `svEqual` y)

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

-- | Values that we can turn into a constraint
class MonadSymbolic m => Constraint m a where
  mkConstraint :: State -> a -> m ()

-- | Base case: simple booleans
instance MonadSymbolic m => Constraint m SBool where
  mkConstraint _ out = void $ output out

-- | An existential symbolic variable, used in building quantified constraints. The name
-- attached via the symbol is used during skolemization to create a skolem-function name
-- when this variable is eliminated.
newtype Exists (nm :: Symbol) a = Exists (SBV a)

-- | An existential unique symbolic variable, used in building quantified constraints. The name
-- attached via the symbol is used during skolemization. It's split into two extra names, suffixed
-- @_eu1@ and @_eu2@, to name the universals in the equivalent formula:
-- \(\exists! x\,P(x)\Leftrightarrow \exists x\,P(x) \land \forall x_{eu1} \forall x_{eu2} (P(x_{eu1}) \land P(x_{eu2}) \Rightarrow x_{eu1} = x_{eu2}) \)
newtype ExistsUnique (nm :: Symbol) a = ExistsUnique (SBV a)

-- | A universal symbolic variable, used in building quantified constraints. The name attached via the symbol is used
-- during skolemization. It names the corresponding argument to the skolem-functions within the scope of this quantifier.
newtype Forall (nm :: Symbol) a = Forall (SBV a)

-- | Exactly @n@ existential symbolic variables, used in building quantified constraints. The name attached
-- will be prefixed in front of @_1@, @_2@, ..., @_n@ to form the names of the variables.
newtype ExistsN (n :: Nat) (nm :: Symbol) a = ExistsN [SBV a]

-- | Exactly @n@ universal symbolic variables, used in in building quantified constraints. The name attached
-- will be prefixed in front of @_1@, @_2@, ..., @_n@ to form the names of the variables.
newtype ForallN (n :: Nat) (nm :: Symbol) a = ForallN [SBV a]

-- | make a quantifier argument in the given state
mkQArg :: forall m a. (HasKind a, MonadIO m) => State -> Quantifier -> m (SBV a)
mkQArg st q = do let k = kindOf (Proxy @a)
                 sv <- liftIO $ quantVar q st k
                 pure $ SBV $ SVal k (Right (cache (const (return sv))))

-- | Functions of a single existential
instance (SymVal a, Constraint m r) => Constraint m (Exists nm a -> r) where
  mkConstraint st fn = mkQArg st EX >>= mkConstraint st . fn . Exists

-- | Functions of a unique single existential
instance (SymVal a, Constraint m r, EqSymbolic (SBV a), QuantifiedBool r) => Constraint m (ExistsUnique nm a -> r) where
  mkConstraint st = mkConstraint st . rewriteExistsUnique

-- | Functions of a number of existentials
instance (KnownNat n, SymVal a, Constraint m r) => Constraint m (ExistsN n nm a -> r) where
  mkConstraint st fn = replicateM (intOfProxy (Proxy @n)) (mkQArg st EX) >>= mkConstraint st . fn . ExistsN

-- | Functions of a single universal
instance (SymVal a, Constraint m r) => Constraint m (Forall nm a -> r) where
  mkConstraint st fn = mkQArg st ALL >>= mkConstraint st . fn . Forall

-- | Functions of a number of universals
instance (KnownNat n, SymVal a, Constraint m r) => Constraint m (ForallN n nm a -> r) where
  mkConstraint st fn = replicateM (intOfProxy (Proxy @n)) (mkQArg st ALL) >>= mkConstraint st . fn . ForallN

-- | Values that we can turn into a lambda abstraction
class MonadSymbolic m => Lambda m a where
  mkLambda :: State -> a -> m ()

-- | Base case, simple values
instance MonadSymbolic m => Lambda m (SBV a) where
  mkLambda _ out = void $ output out

-- | Functions
instance (SymVal a, Lambda m r) => Lambda m (SBV a -> r) where
  mkLambda st fn = mkArg >>= mkLambda st . fn
    where mkArg = do let k = kindOf (Proxy @a)
                     sv <- liftIO $ lambdaVar st k
                     pure $ SBV $ SVal k (Right (cache (const (return sv))))

-- | A value that can be used as a quantified boolean
class QuantifiedBool a where
  -- | Turn a quantified boolean into a regular boolean. That is, this function turns an exists/forall quantified
  -- formula to a simple boolean that can be used as a regular boolean value. An example is:
  --
  -- @
  --   quantifiedBool $ \\(Forall x) (Exists y) -> y .> (x :: SInteger)
  -- @
  --
  -- is equivalent to `sTrue`. You can think of this function as performing quantifier-elimination: It takes
  -- a quantified formula, and reduces it to a simple boolean that is equivalent to it, but has no quantifiers.
  quantifiedBool :: a -> SBool

-- | Base case of quantification, simple booleans
instance {-# OVERLAPPING #-} QuantifiedBool SBool where
  quantifiedBool = id

-- | Actions we can do in a context: Either at problem description
-- time or while we are dynamically querying. 'Symbolic' and 'Query' are
-- two instances of this class. Note that we use this mechanism
-- internally and do not export it from SBV.
class SolverContext m where
   -- | Add a constraint, any satisfying instance must satisfy this condition.
   constrain :: QuantifiedBool a => a -> m ()

   -- | Add a soft constraint. The solver will try to satisfy this condition if possible, but won't if it cannot.
   softConstrain :: QuantifiedBool a => a -> m ()

   -- | Add a named constraint. The name is used in unsat-core extraction.
   namedConstraint :: QuantifiedBool a => String -> a -> m ()

   -- | Add a constraint, with arbitrary attributes.
   constrainWithAttribute :: QuantifiedBool a => [(String, String)] -> a -> m ()

   -- | Set info. Example: @setInfo ":status" ["unsat"]@.
   setInfo :: String -> [String] -> m ()

   -- | Set an option.
   setOption :: SMTOption -> m ()

   -- | Set the logic.
   setLogic :: Logic -> m ()

   -- | Set a solver time-out value, in milli-seconds. This function
   -- essentially translates to the SMTLib call @(set-info :timeout val)@,
   -- and your backend solver may or may not support it! The amount given
   -- is in milliseconds. Also see the function 'Data.SBV.Control.timeOut' for finer level
   -- control of time-outs, directly from SBV.
   setTimeOut :: Integer -> m ()

   -- | Get the state associated with this context
   contextState :: m State

   {-# MINIMAL constrain, softConstrain, namedConstraint, constrainWithAttribute, setOption, contextState #-}

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
  newArray_ :: (MonadSymbolic m, HasKind a, HasKind b) => Maybe (SBV b) -> m (array a b)

  -- | Generalization of 'Data.SBV.newArray'
  newArray  :: (MonadSymbolic m, HasKind a, HasKind b) => String -> Maybe (SBV b) -> m (array a b)

  -- | Create a literal array
  sListArray :: (HasKind a, SymVal b) => b -> [(SBV a, SBV b)] -> array a b

  -- | Read the array element at @a@
  readArray :: array a b -> SBV a -> SBV b

  -- | Update the element at @a@ to be @b@
  writeArray :: SymVal b => array a b -> SBV a -> SBV b -> array a b

  -- | Merge two given arrays on the symbolic condition
  -- Intuitively: @mergeArrays cond a b = if cond then a else b@.
  -- Merging pushes the if-then-else choice down on to elements
  mergeArrays :: SymVal b => SBV Bool -> array a b -> array a b -> array a b

  -- | Internal function, not exported to the user
  newArrayInState :: (HasKind a, HasKind b) => Maybe String -> Either (Maybe (SBV b)) String -> State -> IO (array a b)

  {-# MINIMAL readArray, writeArray, mergeArrays, ((newArray_, newArray) | newArrayInState), sListArray #-}
  newArray_   mbVal = symbolicEnv >>= liftIO . newArrayInState Nothing   (Left mbVal)
  newArray nm mbVal = symbolicEnv >>= liftIO . newArrayInState (Just nm) (Left mbVal)

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

                           let k    = ArrayIndex (IMap.size amap) (sbvContext st)
                               iVal = literal initializer

                           iSV <- sbvToSV st iVal

                           let upd  = IMap.insert (unArrayIndex k) ("array_" ++ show k, ks, ArrayFree (Left (Just iSV)))

                           k `seq` modifyState st rArrayMap upd $ modifyIncState st rNewArrs upd
                           return k

  newArrayInState :: forall a b. (HasKind a, HasKind b) => Maybe String -> Either (Maybe (SBV b)) String -> State -> IO (SArray a b)
  newArrayInState mbNm eiVal st = do mapM_ (registerKind st) [aknd, bknd]
                                     SArray <$> newSArr st (aknd, bknd) (mkNm mbNm) (either (Left . (unSBV <$>)) Right eiVal)
     where mkNm Nothing   t = "array_" ++ show t
           mkNm (Just nm) _ = nm
           aknd = kindOf (Proxy @a)
           bknd = kindOf (Proxy @b)

-- | Symbolic Equality. Note that we can't use Haskell's 'Eq' class since Haskell insists on returning Bool
-- Comparing symbolic values will necessarily return a symbolic value.
--
-- Minimal complete definition: None, if the type is instance of @Generic@. Otherwise '(.==)'.
infix 4 .==, ./=, .===, ./==
class EqSymbolic a where
  -- | Symbolic equality.
  (.==) :: a -> a -> SBool
  -- | Symbolic inequality.
  (./=) :: a -> a -> SBool
  -- | Strong equality. On floats ('SFloat'/'SDouble'), strong equality is object equality; that
  -- is @NaN == NaN@ holds, but @+0 == -0@ doesn't. On other types, (.===) is simply (.==).
  -- Note that (.==) is the /right/ notion of equality for floats per IEEE754 specs, since by
  -- definition @+0 == -0@ and @NaN@ equals no other value including itself. But occasionally
  -- we want to be stronger and state @NaN@ equals @NaN@ and @+0@ and @-0@ are different from
  -- each other. In a context where your type is concrete, simply use `Data.SBV.fpIsEqualObject`. But in
  -- a polymorphic context, use the strong equality instead.
  --
  -- NB. If you do not care about or work with floats, simply use (.==) and (./=).
  (.===) :: a -> a -> SBool
  -- | Negation of strong equality. Equaivalent to negation of (.===) on all types.
  (./==) :: a -> a -> SBool

  -- | Returns (symbolic) 'sTrue' if all the elements of the given list are different.
  distinct :: [a] -> SBool

  -- | Returns (symbolic) `sTrue` if all the elements of the given list are different. The second
  -- list contains exceptions, i.e., if an element belongs to that set, it will be considered
  -- distinct regardless of repetition.
  distinctExcept :: [a] -> [a] -> SBool

  -- | Returns (symbolic) 'sTrue' if all the elements of the given list are the same.
  allEqual :: [a] -> SBool

  -- | Symbolic membership test.
  sElem    :: a -> [a] -> SBool

  -- | Symbolic negated membership test.
  sNotElem :: a -> [a] -> SBool

  x ./=  y = sNot (x .==  y)
  x .=== y = x .== y
  x ./== y = sNot (x .=== y)

  allEqual []     = sTrue
  allEqual (x:xs) = sAll (x .==) xs

  -- Default implementation of 'distinct'. Note that we override
  -- this method for the base types to generate better code.
  distinct []     = sTrue
  distinct (x:xs) = sAll (x ./=) xs .&& distinct xs

  -- Default implementation of 'distinctExcept'. Note that we override
  -- this method for the base types to generate better code.
  distinctExcept es ignored = go es
    where isIgnored = (`sElem` ignored)

          go []     = sTrue
          go (x:xs) = let xOK  = isIgnored x .|| sAll (\y -> isIgnored y .|| x ./= y) xs
                      in xOK .&& go xs

  x `sElem`    xs = sAny (.== x) xs
  x `sNotElem` xs = sNot (x `sElem` xs)

  -- Default implementation for '(.==)' if the type is 'Generic'
  default (.==) :: (G.Generic a, GEqSymbolic (G.Rep a)) => a -> a -> SBool
  (.==) = symbolicEqDefault

-- | Default implementation of symbolic equality, when the underlying type is generic
-- Not exported, used with automatic deriving.
symbolicEqDefault :: (G.Generic a, GEqSymbolic (G.Rep a)) => a -> a -> SBool
symbolicEqDefault x y = symbolicEq (G.from x) (G.from y)

-- | Not exported, used for implementing generic equality.
class GEqSymbolic f where
  symbolicEq :: f a -> f a -> SBool

{-
 - N.B. A V1 instance like the below would be wrong!
 - Why? Because in SBV, we use empty data to mean "uninterpreted" sort; not
 - something that has no constructors. Perhaps that was a bad design
 - decision. So, do not allow equality checking of such values.
instance GEqSymbolic V1 where
  symbolicEq _ _ = sTrue
-}

instance GEqSymbolic U1 where
  symbolicEq _ _ = sTrue

instance (EqSymbolic c) => GEqSymbolic (K1 i c) where
  symbolicEq (K1 x) (K1 y) = x .== y

instance (GEqSymbolic f) => GEqSymbolic (M1 i c f) where
  symbolicEq (M1 x) (M1 y) = symbolicEq x y

instance (GEqSymbolic f, GEqSymbolic g) => GEqSymbolic (f :*: g) where
  symbolicEq (x1 :*: y1) (x2 :*: y2) = symbolicEq x1 x2 .&& symbolicEq y1 y2

instance (GEqSymbolic f, GEqSymbolic g) => GEqSymbolic (f :+: g) where
  symbolicEq (L1 l) (L1 r) = symbolicEq l r
  symbolicEq (R1 l) (R1 r) = symbolicEq l r
  symbolicEq (L1 _) (R1 _) = sFalse
  symbolicEq (R1 _) (L1 _) = sFalse

-- | A class of values that can be skolemized. Note that we don't export this class. Use
-- the 'skolemize' function instead.
class Skolemize a where
  type SkolemsTo a :: Type
  skolem :: String -> [(SVal, String)] -> a -> SkolemsTo a

  -- | Skolemization. For any formula, skolemization gives back an equisatisfiable formula that
  -- has no existential quantifiers in it. You have to provide enough names for all the
  -- existentials in the argument. (Extras OK, so you can pass an infinite list if you like.)
  -- The names should be distinct, and also different from any other uninterpreted name
  -- you might have elsewhere.
  skolemize :: (Constraint Symbolic (SkolemsTo a), Skolemize a) => a -> SkolemsTo a
  skolemize = skolem "" []

  -- | If you use the same names for skolemized arguments in different functions, they will
  -- collide; which is undesirable. Unfortunately there's no easy way for SBV to detect this.
  -- In such cases, use 'taggedSkolemize' to add a scope to the skolem-function names generated.
  taggedSkolemize :: (Constraint Symbolic (SkolemsTo a), Skolemize a) => String -> a -> SkolemsTo a
  taggedSkolemize scope = skolem (scope ++ "_") []

-- | Base case; pure symbolic values
instance Skolemize (SBV a) where
  type SkolemsTo (SBV a) = SBV a
  skolem _ _ = id

-- | Skolemize over a universal quantifier
instance (KnownSymbol nm, Skolemize r) => Skolemize (Forall nm a -> r) where
  type SkolemsTo (Forall nm a -> r) = Forall nm a -> SkolemsTo r
  skolem scope args f arg@(Forall a) = skolem scope (args ++ [(unSBV a, symbolVal (Proxy @nm))]) (f arg)

-- | Skolemize over a number of universal quantifiers
instance (KnownSymbol nm, Skolemize r) => Skolemize (ForallN n nm a -> r) where
  type SkolemsTo (ForallN n nm a -> r) = ForallN n nm a -> SkolemsTo r
  skolem scope args f arg@(ForallN xs) = skolem scope (args ++ zipWith grab xs [(1::Int)..]) (f arg)
    where pre = symbolVal (Proxy @nm)
          grab x i = (unSBV x, pre ++ "_" ++ show i)

-- | Skolemize over an existential quantifier
instance (HasKind a, KnownSymbol nm, Skolemize r) => Skolemize (Exists nm a -> r) where
  type SkolemsTo (Exists nm a -> r) = SkolemsTo r
  skolem scope args f = skolem scope args (f (Exists skolemized))
    where skolemized = SBV $ svUninterpretedNamedArgs (kindOf (Proxy @a)) (scope ++ symbolVal (Proxy @nm)) (UINone True) args

-- | Skolemize over a number of existential quantifiers
instance (HasKind a, KnownNat n, KnownSymbol nm, Skolemize r) => Skolemize (ExistsN n nm a -> r) where
  type SkolemsTo (ExistsN n nm a -> r) = SkolemsTo r
  skolem scope args f = skolem scope args (f (ExistsN skolemized))
    where need   = intOfProxy (Proxy @n)
          prefix = symbolVal (Proxy @nm)
          fs     = [prefix ++ "_" ++ show i | i <- [1 .. need]]
          skolemized = [SBV $ svUninterpretedNamedArgs (kindOf (Proxy @a)) (scope ++ n) (UINone True) args | n <- fs]

-- | Skolemize over a unique existential quantifier
instance (  HasKind a
          , EqSymbolic (SBV a)
          , KnownSymbol nm
          , QuantifiedBool r
          , Skolemize (Forall (AppendSymbol nm "_eu1") a -> Forall (AppendSymbol nm "_eu2") a -> SBool)
         ) => Skolemize (ExistsUnique nm a -> r) where
  type SkolemsTo (ExistsUnique nm a -> r) =  Forall (AppendSymbol nm "_eu1") a
                                          -> Forall (AppendSymbol nm "_eu2") a
                                          -> SBool
  skolem scope args f = skolem scope args (rewriteExistsUnique f (Exists skolemized))
    where skolemized = SBV $ svUninterpretedNamedArgs (kindOf (Proxy @a)) (scope ++ symbolVal (Proxy @nm)) (UINone True) args

-- | Class of things that we can logically negate
class QNot a where
  type NegatesTo a :: Type
  -- | Negation of a quantified formula. This operation essentially lifts 'sNot' to quantified formulae.
  -- Note that you can achieve the same using @'sNot' . 'quantifiedBool'@, but that will hide the
  -- quantifiers, so prefer this version if you want to keep them around.
  qNot :: a -> NegatesTo a

-- | Base case; pure symbolic boolean
instance QNot SBool where
  type NegatesTo SBool = SBool
  qNot = sNot

-- | Negate over a universal quantifier. Switches to existential.
instance QNot r => QNot (Forall nm a -> r) where
  type NegatesTo (Forall nm a -> r) = Exists nm a -> NegatesTo r
  qNot f (Exists a) = qNot (f (Forall a))

-- | Negate over a number of universal quantifiers
instance QNot r => QNot (ForallN nm n a -> r) where
  type NegatesTo (ForallN nm n a -> r) = ExistsN nm n a -> NegatesTo r
  qNot f (ExistsN xs) = qNot (f (ForallN xs))

-- | Negate over an existential quantifier. Switches to universal.
instance QNot r => QNot (Exists nm a -> r) where
  type NegatesTo (Exists nm a -> r) = Forall nm a -> NegatesTo r
  qNot f (Forall a) = qNot (f (Exists a))

-- | Negate over a number of existential quantifiers
instance QNot r => QNot (ExistsN nm n a -> r) where
  type NegatesTo (ExistsN nm n a -> r) = ForallN nm n a -> NegatesTo r
  qNot f (ForallN xs) = qNot (f (ExistsN xs))

-- | Negate over an unique existential quantifier
instance (QNot r, QuantifiedBool r, EqSymbolic (SBV a)) => QNot (ExistsUnique nm a -> r) where
  type NegatesTo (ExistsUnique nm a -> r) =  Forall nm a
                                          -> Exists (AppendSymbol nm "_eu1") a
                                          -> Exists (AppendSymbol nm "_eu2") a
                                          -> SBool
  qNot = qNot . rewriteExistsUnique

-- | Get rid of exists unique.
rewriteExistsUnique :: ( QuantifiedBool b                 -- If b can be turned into a boolean
                       , EqSymbolic (SBV a)               -- If we can do equality on symbolic a's
                       )                                  -- THEN
                    => (ExistsUnique nm a -> b)           -- Given an unique-existential, we can
                    -> Exists nm a                        -- Turn it into an existential
                    -> Forall (AppendSymbol nm "_eu1") a  -- A universal
                    -> Forall (AppendSymbol nm "_eu2") a  -- Another universal
                    -> SBool                                  -- Making sure given holds, and if both univers hold, they're the same
rewriteExistsUnique f (Exists x) (Forall x1) (Forall x2) = fx .&& unique
  where fx    = quantifiedBool $ f (ExistsUnique x)
        fx1   = f (ExistsUnique x1)
        fx2   = f (ExistsUnique x2)

        bothHolds  = quantifiedBool fx1 .&& quantifiedBool fx2
        mustEqual  = x1 .== x2
        unique     = bothHolds .=> mustEqual
