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
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}

module Data.SBV.Core.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64, SInteger, SReal, SFloat, SDouble
 , SFloatingPoint, SFPHalf, SFPBFloat, SFPSingle, SFPDouble, SFPQuad
 , SWord, SInt, WordN, IntN
 , SRational
 , SChar, SString, SList
 , SArray, ArrayModel(..)
 , STuple, STuple2, STuple3, STuple4, STuple5, STuple6, STuple7, STuple8
 , RCSet(..), SSet
 , nan, infinity, sNaN, sInfinity, RoundingMode(..), SRoundingMode
 , SymVal(..), SymValInsts(..), symValKinds, SymVals(..)
 , CV(..), CVal(..), AlgReal(..), AlgRealPoly(..), ExtCV(..), GeneralizedCV(..), isRegularCV, cvSameType, cvToBool
 , mkConstCV , mapCV, mapCV2
 , SV(..), trueSV, falseSV, trueCV, falseCV, normCV
 , SVal(..)
 , sTrue, sFalse, sNot, (.&&), (.||), (.<+>), (.~&), (.~|), (.=>), (.<=>), sAnd, sOr, sAny, sAll, fromBool
 , SBV(..), NodeId(..), mkSymSBV
 , sbvToSV, sbvToSymSV, forceSVArg
 , SBVs(..), foldrSBVs, mapMSBVs, foldrSymSBVs, mapSymSBVs, mapMSymSBVs, mkSBVsM
 , SBVExpr(..), newExpr
 , cache, Cached, uncache, HasKind(..)
 , Op(..), PBOp(..), FPOp(..), StrOp(..), RegExOp(..), SeqOp(..), RegExp(..), NamedSymVar(..), OvOp(..), getTableIndex
 , SBVPgm(..), Symbolic, runSymbolic, State, SInfo(..), getSInfo, getPathCondition, extendPathCondition
 , inSMTMode, SBVRunMode(..), Kind(..), Outputtable(..), Result(..)
 , SolverContext(..), internalConstraint, isCodeGenMode
 , SBVType(..), newUninterpreted
 , Quantifier(..), needsExistentials
 , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension
 , SolverCapabilities(..)
 , extractSymbolicSimulationState
 , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..), TPOptions(..)
 , OptimizeStyle(..), Penalty(..), Objective(..)
 , QueryState(..), QueryT(..), SMTProblem(..), Constraint(..), Lambda(..), Forall(..), Exists(..), ExistsUnique(..), ForallN(..), ExistsN(..)
 , QuantifiedBool(..), EqSymbolic(..), QNot(..), Skolemize(SkolemsTo, skolemize, taggedSkolemize)
 , bvExtract, (#), bvDrop, bvTake
 , registerType
 ) where

import GHC.TypeLits (KnownNat, Nat, Symbol, KnownSymbol, symbolVal, AppendSymbol, type (+), type (-), type (<=), natVal)

import Control.DeepSeq        (NFData(..))
import Control.Monad          (void, replicateM)
import Control.Monad.Trans    (liftIO, MonadIO)
import Data.Int               (Int8, Int16, Int32, Int64)
import Data.Word              (Word8, Word16, Word32, Word64)

import Data.Kind (Type)
import Data.Proxy
import Data.Typeable          (Typeable)

import Data.IORef
import qualified Data.Set as Set (toList)

import GHC.Generics (Generic, U1(..), M1(..), (:*:)(..), K1(..), (:+:)(..))
import qualified GHC.Generics  as G

import System.Random

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Sized
import Data.SBV.Core.SizedFloats
import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Operations

import Data.SBV.Control.Types

import Data.SBV.Utils.Lib
import Data.SBV.Utils.Numeric (RoundingMode(..))

import Test.QuickCheck (Arbitrary(..))

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

-- | A symbolic unsigned bit-vector carrying its size info
type SWord (n :: Nat) = SBV (WordN n)

-- | A symbolic signed bit-vector carrying its size info
type SInt (n :: Nat) = SBV (IntN n)

-- | A symbolic character. Note that this is the full unicode character set.
-- see: <https://smt-lib.org/theories-UnicodeStrings.shtml>
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

-- | Symbolic arrays. A symbolic array is more akin to a function in SMTLib (and thus in SBV),
-- as opposed to contagious-storage with a finite range as found in many programming languages.
-- Additionally, the domain uses object-equality in the SMTLib semantics. Object equality is
-- the same as regular equality for most types, except for IEEE-Floats, where @NaN@ doesn't compare
-- equal to itself and @+0@ and @-0@ are not distinguished. So, if your index type is a float,
-- then @NaN@ can be stored correctly, and @0@ and @-0@ will be distinguished. If you don't use
-- floats, then you can treat this the same as regular equality in Haskell.
type SArray a b = SBV (ArrayModel a b)

-- | Symbolic 'Data.Set'. Note that we use 'RCSet', which supports
-- both regular sets and complements, i.e., those obtained from the
-- universal set (of the right type) by removing elements. Similar to 'SArray'
-- the contents are stored with object equality, which makes a difference if the
-- underlying type contains IEEE Floats.
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

-- | The symbolic variant of 'RoundingMode'
type SRoundingMode = SBV RoundingMode

-- | A 'Show' instance is not particularly "desirable," when the value is symbolic,
-- but we do need this instance as otherwise we cannot simply evaluate Haskell functions
-- that return symbolic values and have their constant values printed easily!
instance Show (SBV a) where
  show (SBV sv) = show sv

instance HasKind a => HasKind (SBV a) where
  kindOf _ = kindOf (Proxy @a)

-- | Convert a symbolic value to a symbolic-word
sbvToSV :: State -> SBV a -> IO SV
sbvToSV st (SBV s) = svToSV st s

-- | A sequence of elements of types @'SBV' a1,...,'SBV' an@ given the list
-- @[a1,...,an]@ of Haskell types
data SBVs as where
  SBVsNil :: SBVs '[]
  SBVsCons :: SBV a -> SBVs as -> SBVs (a ': as)

-- | Fold a function over each 'SBV' value in an 'SBVs' sequence in a manner
-- similar to 'foldr' for lists
foldrSBVs :: (forall a. SBV a -> r -> r) -> r -> SBVs as -> r
foldrSBVs _ r SBVsNil = r
foldrSBVs f r (SBVsCons arg args) = f arg $ foldrSBVs f r args

-- | Map a monadic function over the 'SBV' values in an 'SBVs' sequence in a
-- manner similar to 'mapM' for lists
mapMSBVs :: Monad m => (forall a. SBV a -> m r) -> SBVs as -> m [r]
mapMSBVs f = foldrSBVs (\arg m -> (:) <$> f arg <*> m) (return [])

-- | Fold a function over each 'SBV' value in an 'SBVs' sequence in a manner
-- similar to 'foldr' for lists, using 'SymVal' instances for each value
foldrSymSBVs :: (forall a. SymVal a => SBV a -> r -> r) -> r ->
                SymValInsts as -> SBVs as -> r
foldrSymSBVs _ r _ SBVsNil = r
foldrSymSBVs f r (SymValsCons symvs) (SBVsCons arg args) =
  f arg $ foldrSymSBVs f r symvs args

-- | Map a function over the 'SBV' values in an 'SBVs' sequence in a manner
-- similar to 'map' for lists
mapSymSBVs :: (forall a. SymVal a => SBV a -> r) ->
              SymValInsts as -> SBVs as -> [r]
mapSymSBVs f symvs = foldrSymSBVs (\arg r -> f arg : r) [] symvs

-- | Map a monadic function over the 'SBV' values in an 'SBVs' sequence in a
-- manner similar to 'mapM' for lists
mapMSymSBVs :: Monad m => (forall a. SymVal a => SBV a -> m r) ->
            SymValInsts as -> SBVs as -> m [r]
mapMSymSBVs f symvs =
  foldrSymSBVs (\arg m -> (:) <$> f arg <*> m) (return []) symvs

-- | Build an 'SBVs' sequence of @'SBV' a@ values for each type type @a@ in a
-- 'SymValInsts' sequence using the supplied monadic function
mkSBVsM :: Monad m => SymValInsts as ->
           (forall a. SymVal a => Proxy a -> m (SBV a)) -> m (SBVs as)
mkSBVsM SymValsNil _ = return SBVsNil
mkSBVsM (SymValsCons as) f = SBVsCons <$> f Proxy <*> mkSBVsM as f

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

-- | Exactly @n@ universal symbolic variables, used in building quantified constraints. The name attached
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

-- | Functions of a pair of universals
instance (SymVal a, SymVal b, Constraint m r) => Constraint m ((Forall na a, Forall nb b) -> r) where
  mkConstraint st fn = do a <- mkQArg st ALL
                          b <- mkQArg st ALL
                          mkConstraint st $ fn (Forall a, Forall b)

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

   -- | Get an internal-variable
   internalVariable :: Kind -> m (SBV a)

   {-# MINIMAL constrain, softConstrain, namedConstraint, constrainWithAttribute, setOption, contextState, internalVariable #-}

   -- time-out, logic, and info are  simply options in our implementation, so default implementation suffices
   setTimeOut   = setOption . SetTimeOut
   setLogic     = setOption . SetLogic
   setInfo    k = setOption . SetInfo k

-- | Register a type with the solver. Like 'Data.SBV.Core.Model.registerFunction', This is typically not necessary
-- since SBV will register types as it encounters them automatically. But there are cases
-- where doing this can explicitly can come handy, typically in query contexts.
registerType :: forall a m. (MonadIO m, SolverContext m, HasKind a) => Proxy a -> m ()
registerType _ = do st <- contextState
                    liftIO $ registerKind st (kindOf (Proxy @a))

-- | Various info we use in recoverKinded value
newtype SInfo = SInfo { sInfoKinds :: [Kind] }

-- | Turn state into SInfo
getSInfo :: MonadIO m => State -> m SInfo
getSInfo st = do rk <- liftIO $ readIORef (rUsedKinds st)
                 pure $ SInfo { sInfoKinds = Set.toList rk }

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
class (HasKind a, Typeable a, Arbitrary a) => SymVal a where
  -- | Generalization of 'Data.SBV.mkSymVal'
  mkSymVal :: MonadSymbolic m => VarContext -> Maybe String -> m (SBV a)

  -- | Certain types (ADTs) might need to do further initialization.
  mkSymValInit :: State -> SBV a -> IO ()
  mkSymValInit _ _ = pure ()

  -- | Turn a literal constant to symbolic
  literal :: a -> SBV a

  -- | Extract a literal, from a CV representation
  fromCV :: CV -> a

  -- | Does it concretely satisfy the given predicate?
  isConcretely :: SBV a -> (a -> Bool) -> Bool

  -- | If bounded, what's the min/max value for this type?
  -- If the underlying type is bounded, we have a default below. Otherwise it's nothing.
  minMaxBound :: Maybe (a, a)

  {-# MINIMAL literal, fromCV #-}

  default mkSymVal :: MonadSymbolic m => VarContext -> Maybe String -> m (SBV a)
  mkSymVal vc mbNm = do st <- symbolicEnv
                        liftIO $ do v <- SBV <$> svMkSymVar vc (kindOf (undefined :: a)) mbNm st
                                    mkSymValInit st v
                                    pure v

  default minMaxBound :: Bounded a => Maybe (a, a)
  minMaxBound = Just (minBound, maxBound)

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

  -- | Get the underlying CV, if available
  unlitCV :: SBV a -> Maybe (Kind, CVal)
  unlitCV (SBV (SVal _ (Left (CV k v)))) = Just (k, v)
  unlitCV _                              = Nothing

  -- | Is the symbolic word concrete?
  isConcrete :: SBV a -> Bool
  isConcrete (SBV (SVal _ (Left _))) = True
  isConcrete _                       = False

  -- | Is the symbolic word really symbolic?
  isSymbolic :: SBV a -> Bool
  isSymbolic = not . isConcrete

-- | A sequence of instance dictionaries for each type @ai@ in the type list
-- @[a1,...,an]@
data SymValInsts as where
  SymValsNil :: SymValInsts '[]
  SymValsCons :: SymVal a => SymValInsts as -> SymValInsts (a ': as)

-- | Get the 'Kind' of each type in the type list of a 'SymValInsts' sequence
symValKinds :: SymValInsts as -> [Kind]
symValKinds SymValsNil = []
symValKinds insts@(SymValsCons insts') =
  kindOf (headPrx insts) : symValKinds insts'
  where headPrx :: SymValInsts (b ': bs) -> Proxy b
        headPrx _ = Proxy

-- | A 'SymVals' is a list of types that all satisfy 'SymVal'
class SymVals as where
  symValInsts :: SymValInsts as

instance SymVals '[] where
  symValInsts = SymValsNil

instance (SymVal a, SymVals as) => SymVals (a ': as) where
  symValInsts = SymValsCons symValInsts

instance (Random a, SymVal a) => Random (SBV a) where
  randomR (l, h) g = case (unliteral l, unliteral h) of
                       (Just lb, Just hb) -> let (v, g') = randomR (lb, hb) g in (literal (v :: a), g')
                       _                  -> error "SBV.Random: Cannot generate random values with symbolic bounds"
  random         g = let (v, g') = random g in (literal (v :: a) , g')

-- | Symbolic Equality. Note that we can't use Haskell's 'Eq' class since Haskell insists on returning Bool
-- Comparing symbolic values will necessarily return a symbolic value.
--
-- NB. Equality is a built-in notion in SMTLib, and is object-equality. While this mostly matches Haskell's
-- notion of equality, the correspondence isn't exact. This mostly shows up in containers with floats inside,
-- such as sequences of floats, sets of doubles, and arrays of doubles. While SBV tries to maintain Haskell
-- semantics, it does resort to container equality for compound types. For instance, for an IEEE-float,
-- -0 == 0. But for an SMTLib sequence, equals is done over objects. i.e., @[0] == [-0]@ in Haskell, but
-- @literal [0] ./= literal [-0]@ when used as SMTLib sequences. The rabbit-hole goes deep here, especially
-- when @NaN@ is involved, which does not compare equal to itself per IEEE-semantics.
--
-- If you are not using floats, then you can ignore all this. If you do, then SBV will do the right thing for
-- them when checking equality directly, but not when you use containers with floating-point elements. In the
-- latter case, object-equality will be used.
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

-- We don't want to do a generic Num a => Num (SBV a) instance; since that would be dangerous. Liftings
-- would only work for types we already handle. If a user defines his own type and makes an instance
-- of it, it would do the wrong thing. See https://github.com/LeventErkok/sbv/issues/706 for a discussion.
-- So, we have to declare the instances individually. I played around doing this via iso-deriving and
-- other generic mechanisms, but failed to do so. The CPP solution here is crude, but it avoids the
-- code duplication.
#define MKSNUM(CSTR, TYPE, KIND)                                                        \
instance CSTR => Num TYPE where {                                                       \
  fromInteger i  = SBV $ SVal KIND $ Left $ mkConstCV KIND (fromIntegral i :: Integer); \
  SBV a + SBV b  = SBV $ a `svPlus`  b;                                                 \
  SBV a * SBV b  = SBV $ a `svTimes` b;                                                 \
  SBV a - SBV b  = SBV $ a `svMinus` b;                                                 \
  abs    (SBV a) = SBV $ svAbs    a;                                                    \
  signum (SBV a) = SBV $ svSignum a;                                                    \
  negate (SBV a) = SBV $ svUNeg   a;                                                    \
}

-- Derive basic instances we need. NB. We don't give the SRational instance here. It's handled
-- in Data/SBV/Rational due to representation issues.
MKSNUM((),                 SInteger,               KUnbounded)
MKSNUM((),                 SWord8,                 (KBounded False  8))
MKSNUM((),                 SWord16,                (KBounded False 16))
MKSNUM((),                 SWord32,                (KBounded False 32))
MKSNUM((),                 SWord64,                (KBounded False 64))
MKSNUM((),                 SInt8,                  (KBounded True   8))
MKSNUM((),                 SInt16,                 (KBounded True  16))
MKSNUM((),                 SInt32,                 (KBounded True  32))
MKSNUM((),                 SInt64,                 (KBounded True  64))
MKSNUM((),                 SFloat,                 KFloat)
MKSNUM((),                 SDouble,                KDouble)
MKSNUM((),                 SReal,                  KReal)
MKSNUM((KnownNat n),       (SWord n),              (KBounded False (intOfProxy (Proxy @n))))
MKSNUM((KnownNat n),       (SInt  n),              (KBounded True  (intOfProxy (Proxy @n))))
MKSNUM((ValidFloat eb sb), (SFloatingPoint eb sb), (KFP (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))))
#undef MKSNUM

-- | Extract a portion of bits to form a smaller bit-vector.
bvExtract :: forall i j n bv proxy. ( KnownNat n, BVIsNonZero n, SymVal (bv n)
                                    , KnownNat i
                                    , KnownNat j
                                    , i + 1 <= n
                                    , j <= i
                                    , BVIsNonZero (i - j + 1)
                                    ) => proxy i                -- ^ @i@: Start position, numbered from @n-1@ to @0@
                                      -> proxy j                -- ^ @j@: End position, numbered from @n-1@ to @0@, @j <= i@ must hold
                                      -> SBV (bv n)             -- ^ Input bit vector of size @n@
                                      -> SBV (bv (i - j + 1))   -- ^ Output is of size @i - j + 1@
bvExtract start end = SBV . svExtract i j . unSBV
   where i  = fromIntegral (natVal start)
         j  = fromIntegral (natVal end)

-- | Join two bit-vectors.
(#) :: ( KnownNat n, BVIsNonZero n, SymVal (bv n)
       , KnownNat m, BVIsNonZero m, SymVal (bv m)
       ) => SBV (bv n)                     -- ^ First input, of size @n@, becomes the left side
         -> SBV (bv m)                     -- ^ Second input, of size @m@, becomes the right side
         -> SBV (bv (n + m))               -- ^ Concatenation, of size @n+m@
n # m = SBV $ svJoin (unSBV n) (unSBV m)
infixr 5 #

-- | Drop bits from the top of a bit-vector.
bvDrop :: forall i n m bv proxy. ( KnownNat n, BVIsNonZero n
                                 , KnownNat i
                                 , i + 1 <= n
                                 , i + m - n <= 0
                                 , BVIsNonZero (n - i)
                                 ) => proxy i                    -- ^ @i@: Number of bits to drop. @i < n@ must hold.
                                   -> SBV (bv n)                 -- ^ Input, of size @n@
                                   -> SBV (bv m)                 -- ^ Output, of size @m@. @m = n - i@ holds.
bvDrop i = SBV . svExtract start 0 . unSBV
  where nv    = intOfProxy (Proxy @n)
        start = nv - fromIntegral (natVal i) - 1

-- | Take bits from the top of a bit-vector.
bvTake :: forall i n bv proxy. ( KnownNat n, BVIsNonZero n
                               , KnownNat i, BVIsNonZero i
                               , i <= n
                               ) => proxy i                  -- ^ @i@: Number of bits to take. @0 < i <= n@ must hold.
                                 -> SBV (bv n)               -- ^ Input, of size @n@
                                 -> SBV (bv i)               -- ^ Output, of size @i@
bvTake i = SBV . svExtract start end . unSBV
  where nv    = intOfProxy (Proxy @n)
        start = nv - 1
        end   = start - fromIntegral (natVal i) + 1

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

-- | Skolemize over a o pair universal quantifier
instance (KnownSymbol na, KnownSymbol nb, Skolemize r) => Skolemize ((Forall na a, Forall nb b) -> r) where
  type SkolemsTo ((Forall na a, Forall nb b) -> r) = (Forall na a, Forall nb b) -> SkolemsTo r
  skolem scope args f = uncurry (skolem scope args (curry f))

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
    where skolemized = SBV $ svUninterpretedNamedArgs (kindOf (Proxy @a)) (UIGiven (scope ++ symbolVal (Proxy @nm))) (UINone True) args

-- | Skolemize over a o pair existential quantifier
instance (HasKind a, HasKind b, KnownSymbol na, KnownSymbol nb, Skolemize r) => Skolemize ((Exists na a, Exists nb b) -> r) where
  type SkolemsTo ((Exists na a, Exists nb b) -> r) = SkolemsTo r
  skolem scope args = skolem scope args . curry

-- | Skolemize over a number of existential quantifiers
instance (HasKind a, KnownNat n, KnownSymbol nm, Skolemize r) => Skolemize (ExistsN n nm a -> r) where
  type SkolemsTo (ExistsN n nm a -> r) = SkolemsTo r
  skolem scope args f = skolem scope args (f (ExistsN skolemized))
    where need   = intOfProxy (Proxy @n)
          prefix = symbolVal (Proxy @nm)
          fs     = [prefix ++ "_" ++ show i | i <- [1 .. need]]
          skolemized = [SBV $ svUninterpretedNamedArgs (kindOf (Proxy @a)) (UIGiven (scope ++ n)) (UINone True) args | n <- fs]

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
    where skolemized = SBV $ svUninterpretedNamedArgs (kindOf (Proxy @a)) (UIGiven (scope ++ symbolVal (Proxy @nm))) (UINone True) args

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

-- | Negate over a unique existential quantifier
instance (QNot r, QuantifiedBool r, EqSymbolic (SBV a)) => QNot (ExistsUnique nm a -> r) where
  type NegatesTo (ExistsUnique nm a -> r) =  Forall nm a
                                          -> Exists (AppendSymbol nm "_eu1") a
                                          -> Exists (AppendSymbol nm "_eu2") a
                                          -> SBool
  qNot = qNot . rewriteExistsUnique

-- | Negate over a pair of universals
instance QNot r => QNot ((Forall na a, Forall nb b) -> r) where
  type NegatesTo ((Forall na a, Forall nb b) -> r) = (Exists na a, Exists nb b) -> NegatesTo r
  qNot f (Exists a, Exists b) = qNot (f (Forall a, Forall b))

-- | Negate over a pair of existentials
instance QNot r => QNot ((Exists na a, Exists nb b) -> r) where
  type NegatesTo ((Exists na a, Exists nb b) -> r) = (Forall na a, Forall nb b) -> NegatesTo r
  qNot f (Forall a, Forall b) = qNot (f (Exists a, Exists b))

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
