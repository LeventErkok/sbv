-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Symbolic
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic values
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Core.Symbolic
  ( NodeId(..)
  , SV(..), swKind, trueSV, falseSV, contextOfSV
  , Op(..), PBOp(..), OvOp(..), FPOp(..), NROp(..), StrOp(..), RegExOp(..), SeqOp(..), SetOp(..), SpecialRelOp(..)
  , RegExp(..), regExpToSMTString
  , Quantifier(..), needsExistentials, SBVContext(..), checkCompatibleContext, VarContext(..)
  , RoundingMode(..)
  , SBVType(..), svUninterpreted, svUninterpretedNamedArgs, newUninterpreted
  , SVal(..)
  , svMkSymVar, sWordN, sWordN_, sIntN, sIntN_
  , ArrayContext(..), ArrayInfo
  , svToSV, svToSymSV, forceSVArg
  , SBVExpr(..), newExpr, isCodeGenMode, isSafetyCheckingIStage, isRunIStage, isSetupIStage
  , Cached, cache, uncache, modifyState, modifyIncState
  , ArrayIndex(..), uncacheAI
  , NamedSymVar(..), Name, UserInputs, Inputs(..), getSV, swNodeId, namedNodeId
  , addInternInput, addUserInput
  , getUserName', getUserName
  , lookupInput , getSValPathCondition, extendSValPathCondition
  , getTableIndex
  , SBVPgm(..), MonadSymbolic(..), SymbolicT, Symbolic, runSymbolic, mkNewState, runSymbolicInState, State(..), SMTDef(..), smtDefGivenName, withNewIncState, IncState(..), incrementInternalCounter
  , inSMTMode, SBVRunMode(..), IStage(..), Result(..), ResultInp(..), UICodeKind(..)
  , registerKind, registerLabel, recordObservable
  , addAssertion, addNewSMTOption, imposeConstraint, internalConstraint, internalVariable, lambdaVar, quantVar
  , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension
  , SolverCapabilities(..)
  , extractSymbolicSimulationState, CnstMap
  , OptimizeStyle(..), Objective(..), Penalty(..), objectiveName, addSValOptGoal
  , MonadQuery(..), QueryT(..), Query, Queriable(..), Fresh(..), QueryState(..), QueryContext(..)
  , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..), SMTEngine
  , validationRequested, outputSVal, ProgInfo(..), mustIgnoreVar, getRootState
  ) where

import Control.DeepSeq             (NFData(..))
import Control.Monad               (when)
import Control.Monad.Except        (MonadError, ExceptT)
import Control.Monad.Reader        (MonadReader(..), ReaderT, runReaderT,
                                    mapReaderT)
import Control.Monad.State.Lazy    (MonadState)
import Control.Monad.Trans         (MonadIO(liftIO), MonadTrans(lift))
import Control.Monad.Trans.Maybe   (MaybeT)
import Control.Monad.Writer.Strict (MonadWriter)
import Data.Char                   (isAlpha, isAlphaNum, toLower)
import Data.IORef                  (IORef, newIORef, readIORef)
import Data.List                   (intercalate, sortBy, isPrefixOf, isSuffixOf, nub)
import Data.Maybe                  (fromMaybe, mapMaybe)
import Data.String                 (IsString(fromString))
import Data.Kind                   (Type)

import Data.Time (getCurrentTime, UTCTime)

import Data.Int (Int64)

import GHC.Stack
import GHC.Stack.Types
import GHC.Generics (Generic)

import qualified Control.Monad.State.Lazy    as LS
import qualified Control.Monad.State.Strict  as SS
import qualified Control.Monad.Writer.Lazy   as LW
import qualified Control.Monad.Writer.Strict as SW
import qualified Data.IORef                  as R    (modifyIORef')
import qualified Data.Generics               as G    (Data(..))
import qualified Data.Generics.Uniplate.Data as G
import qualified Data.IntMap.Strict          as IMap (IntMap, empty, toAscList, lookup, insertWith)
import qualified Data.Map.Strict             as Map  (Map, empty, toList, lookup, insert, size)
import qualified Data.Set                    as Set  (Set, empty, toList, insert, member)
import qualified Data.Foldable               as F    (toList)
import qualified Data.Sequence               as S    (Seq, empty, (|>), (<|), lookup, elemIndexL)
import qualified Data.Text                   as T

import System.Mem.StableName
import System.Random

import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.SMT.SMTLibNames
import Data.SBV.Utils.TDiff (Timing)
import Data.SBV.Utils.Lib   (stringToQFS)

import Data.SBV.Control.Types

#if MIN_VERSION_base(4,11,0)
import Control.Monad.Fail as Fail
#endif

-- | Context identifier. 0 is reserved global context
newtype SBVContext = SBVContext Int64 deriving (Eq, Ord, G.Data, Show)

instance NFData SBVContext where
  rnf (SBVContext i) = i `seq` ()

-- | Global context
globalSBVContext :: SBVContext
globalSBVContext = SBVContext 0

-- | Generate context. We make sure it isn't 0, i.e., the global context
-- The "hope" here is that each time we call this we get a different context number.
-- A random number doesn't necessarily have to do that, but I think the pseudo-generator
-- has a large enough period for this to go through OK.
genSBVContext :: IO SBVContext
genSBVContext = do ctx <- SBVContext <$> randomIO
                   if ctx == globalSBVContext   -- unlikely, but possible
                      then genSBVContext
                      else pure ctx

-- | A symbolic node id
newtype NodeId = NodeId { getId :: (SBVContext, Int, Int) } -- Lambda-level, and node-id
  deriving (Ord, G.Data)

-- Equality is pair-wise, except we accommodate for negative node-id; which is reserved for true/false
instance Eq NodeId where
  NodeId n1@(_, _, i) == NodeId n2@(_, _, j)
     | i < 0 && j < 0
     = i == j
     | True
     = n1 == n2

-- | A symbolic word, tracking it's signedness and size.
data SV = SV !Kind !NodeId
        deriving G.Data

-- | Which context are we using this var at?
contextOfSV :: SV -> SBVContext
contextOfSV (SV _ (NodeId (c, _, _))) = c

-- | For equality, we merely use the lambda-level/node-id
instance Eq SV where
  SV _ n1 == SV _ n2 = n1 == n2

-- | Again, simply use the lambda-level/node-id for ordering
instance Ord SV where
  SV _ n1 `compare` SV _ n2 = n1 `compare` n2

instance HasKind SV where
  kindOf (SV k _) = k

instance Show SV where
  show (SV _ (NodeId (_, l, n))) = case n of
                                     -2 -> "false"
                                     -1 -> "true"
                                     _  -> prefix ++ 's' : show n
        where prefix = case l of
                         0 -> ""
                         _ -> 'l' : show l ++ "_"

-- | Kind of a symbolic word.
swKind :: SV -> Kind
swKind (SV k _) = k

-- | retrieve the node id of a symbolic word
swNodeId :: SV -> NodeId
swNodeId (SV _ nid) = nid

-- | Forcing an argument; this is a necessary evil to make sure all the arguments
-- to an uninterpreted function are evaluated before called; the semantics of uinterpreted
-- functions is necessarily strict; deviating from Haskell's
forceSVArg :: SV -> IO ()
forceSVArg (SV k n) = k `seq` n `seq` return ()

-- | Constant False as an 'SV'. Note that this value always occupies slot -2 and level 0.
falseSV :: SV
falseSV = SV KBool $ NodeId (globalSBVContext, 0, -2)

-- | Constant True as an 'SV'. Note that this value always occupies slot -1 and level 0.
trueSV :: SV
trueSV  = SV KBool $ NodeId (globalSBVContext, 0, -1)

-- | Symbolic operations
data Op = Plus
        | Times
        | Minus
        | UNeg
        | Abs
        | Quot
        | Rem
        | Equal
        | Implies
        | NotEqual
        | LessThan
        | GreaterThan
        | LessEq
        | GreaterEq
        | Ite
        | And
        | Or
        | XOr
        | Not
        | Shl
        | Shr
        | Rol Int
        | Ror Int
        | Extract Int Int                       -- Extract i j: extract bits i to j. Least significant bit is 0 (big-endian)
        | Join                                  -- Concat two words to form a bigger one, in the order given
        | ZeroExtend Int
        | SignExtend Int
        | LkUp (Int, Kind, Kind, Int) !SV !SV   -- (table-index, arg-type, res-type, length of the table) index out-of-bounds-value
        | ArrEq   ArrayIndex ArrayIndex         -- Array equality
        | ArrRead ArrayIndex
        | KindCast Kind Kind
        | Uninterpreted String
        | QuantifiedBool String                 -- When we generate a forall/exists (nested etc.) boolean value
        | SpecialRelOp Kind SpecialRelOp        -- Generate the equality to the internal operation
        | Label String                          -- Essentially no-op; useful for code generation to emit comments.
        | IEEEFP FPOp                           -- Floating-point ops, categorized separately
        | NonLinear NROp                        -- Non-linear ops (mostly trigonometric), categorized separately
        | OverflowOp    OvOp                    -- Overflow-ops, categorized separately
        | PseudoBoolean PBOp                    -- Pseudo-boolean ops, categorized separately
        | RegExOp RegExOp                       -- RegEx operations, categorized separately
        | StrOp StrOp                           -- String ops, categorized separately
        | SeqOp SeqOp                           -- Sequence ops, categorized separately
        | SetOp SetOp                           -- Set operations, categorized separately
        | TupleConstructor Int                  -- Construct an n-tuple
        | TupleAccess Int Int                   -- Access element i of an n-tuple; second argument is n
        | EitherConstructor Kind Kind Bool      -- Construct a sum; False: left, True: right
        | EitherIs Kind Kind Bool               -- Either branch tester; False: left, True: right
        | EitherAccess Bool                     -- Either branch access; False: left, True: right
        | RationalConstructor                   -- Construct a rational. Note that there's no access to numerator or denumerator, since we cannot store rationals in canonical form
        | MaybeConstructor Kind Bool            -- Construct a maybe value; False: Nothing, True: Just
        | MaybeIs Kind Bool                     -- Maybe tester; False: nothing, True: just
        | MaybeAccess                           -- Maybe branch access; grab the contents of the just
        deriving (Eq, Ord, G.Data)

-- | Special relations supported by z3
data SpecialRelOp = IsPartialOrder         String
                  | IsLinearOrder          String
                  | IsTreeOrder            String
                  | IsPiecewiseLinearOrder String
                  deriving (Eq, Ord, G.Data, Show)

instance NFData SpecialRelOp where
  rnf (IsPartialOrder         n) = rnf n
  rnf (IsLinearOrder          n) = rnf n
  rnf (IsTreeOrder            n) = rnf n
  rnf (IsPiecewiseLinearOrder n) = rnf n

-- | Floating point operations
data FPOp = FP_Cast        Kind Kind SV   -- From-Kind, To-Kind, RoundingMode. This is "value" conversion
          | FP_Reinterpret Kind Kind      -- From-Kind, To-Kind. This is bit-reinterpretation using IEEE-754 interchange format
          | FP_Abs
          | FP_Neg
          | FP_Add
          | FP_Sub
          | FP_Mul
          | FP_Div
          | FP_FMA
          | FP_Sqrt
          | FP_Rem
          | FP_RoundToIntegral
          | FP_Min
          | FP_Max
          | FP_ObjEqual
          | FP_IsNormal
          | FP_IsSubnormal
          | FP_IsZero
          | FP_IsInfinite
          | FP_IsNaN
          | FP_IsNegative
          | FP_IsPositive
          deriving (Eq, Ord, G.Data)

-- Note that the show instance maps to the SMTLib names. We need to make sure
-- this mapping stays correct through SMTLib changes. The only exception
-- is FP_Cast; where we handle different source/origins explicitly later on.
instance Show FPOp where
   show (FP_Cast f t r)      = "(FP_Cast: " ++ show f ++ " -> " ++ show t ++ ", using RM [" ++ show r ++ "])"
   show (FP_Reinterpret f t) = case t of
                                  KFloat    -> "(_ to_fp 8 24)"
                                  KDouble   -> "(_ to_fp 11 53)"
                                  KFP eb sb -> "(_ to_fp " ++ show eb ++ " " ++ show sb ++ ")"
                                  _         -> error $ "SBV.FP_Reinterpret: Unexpected conversion: " ++ show f ++ " to " ++ show t
   show FP_Abs               = "fp.abs"
   show FP_Neg               = "fp.neg"
   show FP_Add               = "fp.add"
   show FP_Sub               = "fp.sub"
   show FP_Mul               = "fp.mul"
   show FP_Div               = "fp.div"
   show FP_FMA               = "fp.fma"
   show FP_Sqrt              = "fp.sqrt"
   show FP_Rem               = "fp.rem"
   show FP_RoundToIntegral   = "fp.roundToIntegral"
   show FP_Min               = "fp.min"
   show FP_Max               = "fp.max"
   show FP_ObjEqual          = "="
   show FP_IsNormal          = "fp.isNormal"
   show FP_IsSubnormal       = "fp.isSubnormal"
   show FP_IsZero            = "fp.isZero"
   show FP_IsInfinite        = "fp.isInfinite"
   show FP_IsNaN             = "fp.isNaN"
   show FP_IsNegative        = "fp.isNegative"
   show FP_IsPositive        = "fp.isPositive"

-- | Non-linear operations
data NROp = NR_Sin
          | NR_Cos
          | NR_Tan
          | NR_ASin
          | NR_ACos
          | NR_ATan
          | NR_Sqrt
          | NR_Sinh
          | NR_Cosh
          | NR_Tanh
          | NR_Exp
          | NR_Log
          | NR_Pow
          deriving (Eq, Ord, G.Data)

-- | The show instance carefully arranges for these to be printed as it can be understood by dreal
instance Show NROp where
  show NR_Sin  = "sin"
  show NR_Cos  = "cos"
  show NR_Tan  = "tan"
  show NR_ASin = "asin"
  show NR_ACos = "acos"
  show NR_ATan = "atan"
  show NR_Sinh = "sinh"
  show NR_Cosh = "cosh"
  show NR_Tanh = "tanh"
  show NR_Sqrt = "sqrt"
  show NR_Exp  = "exp"
  show NR_Log  = "log"
  show NR_Pow  = "pow"

-- | Pseudo-boolean operations
data PBOp = PB_AtMost  Int        -- ^ At most k
          | PB_AtLeast Int        -- ^ At least k
          | PB_Exactly Int        -- ^ Exactly k
          | PB_Le      [Int] Int  -- ^ At most k,  with coefficients given. Generalizes PB_AtMost
          | PB_Ge      [Int] Int  -- ^ At least k, with coefficients given. Generalizes PB_AtLeast
          | PB_Eq      [Int] Int  -- ^ Exactly k,  with coefficients given. Generalized PB_Exactly
          deriving (Eq, Ord, Show, G.Data)

-- | Overflow operations
data OvOp = PlusOv Bool           -- ^ Addition    overflow.    Bool is True if signed.
          | SubOv  Bool           -- ^ Subtraction overflow.    Bool is True if signed.
          | MulOv  Bool           -- ^ Multiplication overflow. Bool is True if signed.
          | DivOv                 -- ^ Division overflow.       Only signed, since unsigned division does not overflow.
          | NegOv                 -- ^ Unary negation overflow. Only signed, since unsigned negation does not overflow.
          deriving (Eq, Ord, G.Data)

-- | Show instance. It's important that these follow the SMTLib names.
instance Show OvOp where
  show (PlusOv signed) = "bv" ++ (if signed then "s" else "u") ++ "addo"
  show (SubOv  signed) = "bv" ++ (if signed then "s" else "u") ++ "subo"
  show (MulOv  signed) = "bv" ++ (if signed then "s" else "u") ++ "mulo"
  show DivOv           = "bvsdivo" -- This is confusing, the division is called bvsdivo, but negation is bvnego
  show NegOv           = "bvnego"  -- But SMTLib's choice is deliberate: https://groups.google.com/u/0/g/smt-lib/c/J4D99wT0aKI

-- | String operations. Note that we do not define @StrAt@ as it translates to 'StrSubstr' trivially.
data StrOp = StrConcat       -- ^ Concatenation of one or more strings
           | StrLen          -- ^ String length
           | StrUnit         -- ^ Unit string
           | StrNth          -- ^ Nth element
           | StrSubstr       -- ^ Retrieves substring of @s@ at @offset@
           | StrIndexOf      -- ^ Retrieves first position of @sub@ in @s@, @-1@ if there are no occurrences
           | StrContains     -- ^ Does @s@ contain the substring @sub@?
           | StrPrefixOf     -- ^ Is @pre@ a prefix of @s@?
           | StrSuffixOf     -- ^ Is @suf@ a suffix of @s@?
           | StrReplace      -- ^ Replace the first occurrence of @src@ by @dst@ in @s@
           | StrStrToNat     -- ^ Retrieve integer encoded by string @s@ (ground rewriting only)
           | StrNatToStr     -- ^ Retrieve string encoded by integer @i@ (ground rewriting only)
           | StrToCode       -- ^ Equivalent to Haskell's ord
           | StrFromCode     -- ^ Equivalent to Haskell's chr
           | StrInRe RegExp  -- ^ Check if string is in the regular expression
           deriving (Eq, Ord, G.Data)

-- | Regular-expression operators. The only thing we can do is to compare for equality/disequality.
data RegExOp = RegExEq  RegExp RegExp
             | RegExNEq RegExp RegExp
             deriving (Eq, Ord, G.Data)

-- | Regular expressions. Note that regular expressions themselves are
-- concrete, but the 'Data.SBV.RegExp.match' function from the 'Data.SBV.RegExp.RegExpMatchable' class
-- can check membership against a symbolic string/character. Also, we
-- are preferring a datatype approach here, as opposed to coming up with
-- some string-representation; there are way too many alternatives
-- already so inventing one isn't a priority. Please get in touch if you
-- would like a parser for this type as it might be easier to use.
data RegExp = Literal String       -- ^ Precisely match the given string
            | All                  -- ^ Accept every string
            | AllChar              -- ^ Accept every single character
            | None                 -- ^ Accept no strings
            | Range Char Char      -- ^ Accept range of characters
            | Conc  [RegExp]       -- ^ Concatenation
            | KStar RegExp         -- ^ Kleene Star: Zero or more
            | KPlus RegExp         -- ^ Kleene Plus: One or more
            | Opt   RegExp         -- ^ Zero or one
            | Comp  RegExp         -- ^ Complement of regular expression
            | Diff  RegExp RegExp  -- ^ Difference of regular expressions
            | Loop  Int Int RegExp -- ^ From @n@ repetitions to @m@ repetitions
            | Power Int     RegExp -- ^ Exactly @n@ repetitions, i.e., nth power
            | Union [RegExp]       -- ^ Union of regular expressions
            | Inter RegExp RegExp  -- ^ Intersection of regular expressions
            deriving (Eq, Ord, G.Data)

-- | With overloaded strings, we can have direct literal regular expressions.
instance IsString RegExp where
  fromString = Literal

-- | Regular expressions as a 'Num' instance. Note that only some operations make sense and
-- not in the most obvious way. For instance, we would typically expect @a - b@ to be the
-- same as @a + negate b@, but that equality does not hold in general. So, use the @Num@
-- instance only as constructing syntax, not doing algebraic manipulations.
instance Num RegExp where
  -- flatten the concats to make them simpler
  Conc xs * y = Conc (xs ++ [y])
  x * Conc ys = Conc (x  :  ys)
  x * y       = Conc [x, y]

  -- flatten the unions to make them simpler
  Union xs + y = Union (xs ++ [y])
  x + Union ys = Union (x  : ys)
  x + y        = Union [x, y]

  x - y = Diff x y

  abs         = error "Num.RegExp: no abs method"
  signum      = error "Num.RegExp: no signum method"

  fromInteger x
    | x == 0    = None
    | x == 1    = Literal ""   -- Unit for concatenation is the empty string
    | True      = error $ "Num.RegExp: Only 0 and 1 makes sense as a reg-exp, no meaning for: " ++ show x

  negate = Comp

-- | Convert a reg-exp to a Haskell-like string
instance Show RegExp where
  show = regExpToString show

-- | Convert a reg-exp to a SMT-lib acceptable representation
regExpToSMTString :: RegExp -> String
regExpToSMTString = regExpToString (\s -> '"' : stringToQFS s ++ "\"")

-- | Convert a RegExp to a string, parameterized by how strings are converted
regExpToString :: (String -> String) -> RegExp -> String
regExpToString fs (Literal s)       = "(str.to.re " ++ fs s ++ ")"
regExpToString _  All               = "re.all"
regExpToString _  AllChar           = "re.allchar"
regExpToString _  None              = "re.nostr"
regExpToString fs (Range ch1 ch2)   = "(re.range " ++ fs [ch1] ++ " " ++ fs [ch2] ++ ")"
regExpToString _  (Conc [])         = show (1 :: Integer)
regExpToString fs (Conc [x])        = regExpToString fs x
regExpToString fs (Conc xs)         = "(re.++ " ++ unwords (map (regExpToString fs) xs) ++ ")"
regExpToString fs (KStar r)         = "(re.* " ++ regExpToString fs r ++ ")"
regExpToString fs (KPlus r)         = "(re.+ " ++ regExpToString fs r ++ ")"
regExpToString fs (Opt   r)         = "(re.opt " ++ regExpToString fs r ++ ")"
regExpToString fs (Comp  r)         = "(re.comp " ++ regExpToString fs r ++ ")"
regExpToString fs (Diff  r1 r2)     = "(re.diff " ++ regExpToString fs r1 ++ " " ++ regExpToString fs r2 ++ ")"
regExpToString fs (Loop  lo hi r)
   | lo >= 0, hi >= lo = "((_ re.loop " ++ show lo ++ " " ++ show hi ++ ") " ++ regExpToString fs r ++ ")"
   | True              = error $ "Invalid regular-expression Loop with arguments: " ++ show (lo, hi)
regExpToString fs (Power n r)
   | n >= 0            = regExpToString fs (Loop n n r)
   | True              = error $ "Invalid regular-expression Power with arguments: " ++ show n
regExpToString fs (Inter r1 r2)     = "(re.inter " ++ regExpToString fs r1 ++ " " ++ regExpToString fs r2 ++ ")"
regExpToString _  (Union [])        = "re.nostr"
regExpToString fs (Union [x])       = regExpToString fs x
regExpToString fs (Union xs)        = "(re.union " ++ unwords (map (regExpToString fs) xs) ++ ")"

-- | Show instance for @StrOp@. Note that the mapping here is important to match the SMTLib equivalents.
instance Show StrOp where
  show StrConcat   = "str.++"
  show StrLen      = "str.len"
  show StrUnit     = "str.unit"      -- NB. This is actually a no-op, since in SMTLib characters are the same as strings.
  show StrNth      = "str.at"
  show StrSubstr   = "str.substr"
  show StrIndexOf  = "str.indexof"
  show StrContains = "str.contains"
  show StrPrefixOf = "str.prefixof"
  show StrSuffixOf = "str.suffixof"
  show StrReplace  = "str.replace"
  show StrStrToNat = "str.to.int"    -- NB. SMTLib uses "int" here though only nats are supported
  show StrNatToStr = "int.to.str"    -- NB. SMTLib uses "int" here though only nats are supported
  show StrToCode   = "str.to_code"
  show StrFromCode = "str.from_code"
  -- Note the breakage here with respect to argument order. We fix this explicitly later.
  show (StrInRe s) = "str.in.re " ++ regExpToSMTString s

-- | Show instance for @RegExOp@.
instance Show RegExOp where
  show (RegExEq  r1 r2) = "(= "        ++ regExpToSMTString r1 ++ " " ++ regExpToSMTString r2 ++ ")"
  show (RegExNEq r1 r2) = "(distinct " ++ regExpToSMTString r1 ++ " " ++ regExpToSMTString r2 ++ ")"

-- | Sequence operations.
data SeqOp = SeqConcat            -- ^ See StrConcat
           | SeqLen               -- ^ See StrLen
           | SeqUnit              -- ^ See StrUnit
           | SeqNth               -- ^ See StrNth
           | SeqSubseq            -- ^ See StrSubseq
           | SeqIndexOf           -- ^ See StrIndexOf
           | SeqContains          -- ^ See StrContains
           | SeqPrefixOf          -- ^ See StrPrefixOf
           | SeqSuffixOf          -- ^ See StrSuffixOf
           | SeqReplace           -- ^ See StrReplace
           | SeqMap       String  -- ^ Mapping over sequences
           | SeqMapI      String  -- ^ Mapping over sequences with offset
           | SeqFoldLeft  String  -- ^ Folding of sequences
           | SeqFoldLeftI String  -- ^ Folding of sequences with offset
           | SBVReverse Kind      -- ^ Reversal of sequences. NB. Also works for strings; hence the name.
  deriving (Eq, Ord, G.Data)

-- | Show instance for SeqOp. Again, mapping is important.
instance Show SeqOp where
  show SeqConcat        = "seq.++"
  show SeqLen           = "seq.len"
  show SeqUnit          = "seq.unit"
  show SeqNth           = "seq.nth"
  show SeqSubseq        = "seq.extract"
  show SeqIndexOf       = "seq.indexof"
  show SeqContains      = "seq.contains"
  show SeqPrefixOf      = "seq.prefixof"
  show SeqSuffixOf      = "seq.suffixof"
  show SeqReplace       = "seq.replace"
  show (SeqMap       s) = "seq.map "    ++ s
  show (SeqMapI      s) = "seq.mapi "   ++ s
  show (SeqFoldLeft  s) = "seq.foldl "  ++ s
  show (SeqFoldLeftI s) = "seq.foldli " ++ s

  -- Note: This isn't part of SMTLib, we explicitly handle it
  show (SBVReverse k) = "sbv.reverse[" ++ show k ++ "]"

-- | Set operations.
data SetOp = SetEqual
           | SetMember
           | SetInsert
           | SetDelete
           | SetIntersect
           | SetUnion
           | SetSubset
           | SetDifference
           | SetComplement
        deriving (Eq, Ord, G.Data)

-- The show instance for 'SetOp' is merely for debugging, we map them separately so
-- the mapped strings are less important here.
instance Show SetOp where
  show SetEqual      = "=="
  show SetMember     = "Set.member"
  show SetInsert     = "Set.insert"
  show SetDelete     = "Set.delete"
  show SetIntersect  = "Set.intersect"
  show SetUnion      = "Set.union"
  show SetSubset     = "Set.subset"
  show SetDifference = "Set.difference"
  show SetComplement = "Set.complement"

-- Show instance for 'Op'. Note that this is largely for debugging purposes, not used
-- for being read by any tool.
instance Show Op where
  show Shl    = "<<"
  show Shr    = ">>"

  show (Rol i) = "<<<" ++ show i
  show (Ror i) = ">>>" ++ show i

  show (Extract i j) = "choose [" ++ show i ++ ":" ++ show j ++ "]"

  show (LkUp (ti, at, rt, l) i e)
        = "lookup(" ++ tinfo ++ ", " ++ show i ++ ", " ++ show e ++ ")"
        where tinfo = "table" ++ show ti ++ "(" ++ show at ++ " -> " ++ show rt ++ ", " ++ show l ++ ")"

  show (ArrEq i j)          = "array_" ++ show i ++ " == array_" ++ show j
  show (ArrRead i)          = "select array_" ++ show i

  show (KindCast fr to)     = "cast_" ++ show fr ++ "_" ++ show to
  show (Uninterpreted i)    = "[uninterpreted] " ++ i
  show (QuantifiedBool i)   = "[quantified boolean] " ++ i

  show (Label s)            = "[label] " ++ s

  show (IEEEFP w)           = show w

  show (NonLinear w)        = show w

  show (PseudoBoolean p)    = show p

  show (OverflowOp o)       = show o

  show (StrOp s)            = show s
  show (RegExOp s)          = show s
  show (SeqOp s)            = show s
  show (SetOp s)            = show s

  show (TupleConstructor   0) = "mkSBVTuple0"
  show (TupleConstructor   n) = "mkSBVTuple" ++ show n
  show (TupleAccess      i n) = "proj_" ++ show i ++ "_SBVTuple" ++ show n

  -- Remember, while we try to maintain SMTLib compabitibility here, these output
  -- is merely for debugging purposes. For how we actually render these in SMTLib,
  -- look at the file SBV/SMT/SMTLib2.hs for these constructors.
  show (EitherConstructor k1 k2  False) = "(_ left_SBVEither "  ++ show (KEither k1 k2) ++ ")"
  show (EitherConstructor k1 k2  True ) = "(_ right_SBVEither " ++ show (KEither k1 k2) ++ ")"
  show (EitherIs          k1 k2  False) = "(_ is (left_SBVEither ("  ++ show k1 ++ ") " ++ show (KEither k1 k2) ++ "))"
  show (EitherIs          k1 k2  True ) = "(_ is (right_SBVEither (" ++ show k2 ++ ") " ++ show (KEither k1 k2) ++ "))"
  show (EitherAccess             False) = "get_left_SBVEither"
  show (EitherAccess             True ) = "get_right_SBVEither"
  show RationalConstructor              = "SBV.Rational"
  show (MaybeConstructor k False)       = "(_ nothing_SBVMaybe " ++ show (KMaybe k) ++ ")"
  show (MaybeConstructor k True)        = "(_ just_SBVMaybe "    ++ show (KMaybe k) ++ ")"
  show (MaybeIs          k False)       = "(_ is (nothing_SBVMaybe () "              ++ show (KMaybe k) ++ "))"
  show (MaybeIs          k True )       = "(_ is (just_SBVMaybe (" ++ show k ++ ") " ++ show (KMaybe k) ++ "))"
  show MaybeAccess                      = "get_just_SBVMaybe"

  show op
    | Just s <- op `lookup` syms = s
    | True                       = error "impossible happened; can't find op!"
    where syms = [ (Plus, "+"), (Times, "*"), (Minus, "-"), (UNeg, "-"), (Abs, "abs")
                 , (Quot, "quot")
                 , (Rem,  "rem")
                 , (Equal, "=="), (NotEqual, "/="), (Implies, "=>")
                 , (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<="), (GreaterEq, ">=")
                 , (Ite, "if_then_else")
                 , (And, "&"), (Or, "|"), (XOr, "^"), (Not, "~")
                 , (Join, "#")
                 ]

-- | Quantifiers: forall or exists. Note that we allow arbitrary nestings.
data Quantifier = ALL | EX deriving (Eq, G.Data)

-- | Show instance for 'Quantifier'
instance Show Quantifier where
  show ALL = "Forall"
  show EX  = "Exists"

-- | Which context is this variable being created?
data VarContext = NonQueryVar (Maybe Quantifier)  -- in this case, it can be quantified
                | QueryVar                        -- in this case, it is always existential

-- | Are there any existential quantifiers?
needsExistentials :: [Quantifier] -> Bool
needsExistentials = (EX `elem`)

-- | A simple type for SBV computations, used mainly for uninterpreted constants.
-- We keep track of the signedness/size of the arguments. A non-function will
-- have just one entry in the list.
newtype SBVType = SBVType [Kind]
                deriving (Eq, Ord, G.Data)

instance Show SBVType where
  show (SBVType []) = error "SBV: internal error, empty SBVType"
  show (SBVType xs) = intercalate " -> " $ map show xs

-- | A symbolic expression
data SBVExpr = SBVApp !Op ![SV]
             deriving (Eq, Ord, G.Data)

-- | To improve hash-consing, take advantage of commutative operators by
-- reordering their arguments.
reorder :: SBVExpr -> SBVExpr
reorder s = case s of
              SBVApp op [a, b] | isCommutative op && a > b -> SBVApp op [b, a]
              _ -> s
  where isCommutative :: Op -> Bool
        isCommutative o = o `elem` [Plus, Times, Equal, NotEqual, And, Or, XOr]

-- Show instance for 'SBVExpr'. Again, only for debugging purposes.
instance Show SBVExpr where
  show (SBVApp Ite [t, a, b])             = unwords ["if", show t, "then", show a, "else", show b]
  show (SBVApp Shl     [a, i])            = unwords [show a, "<<", show i]
  show (SBVApp Shr     [a, i])            = unwords [show a, ">>", show i]
  show (SBVApp (Rol i) [a])               = unwords [show a, "<<<", show i]
  show (SBVApp (Ror i) [a])               = unwords [show a, ">>>", show i]
  show (SBVApp (PseudoBoolean pb) args)   = unwords (show pb : map show args)
  show (SBVApp (OverflowOp op)    args)   = unwords (show op : map show args)
  show (SBVApp op                 [a, b]) = unwords [show a, show op, show b]
  show (SBVApp op                 args)   = unwords (show op : map show args)

-- | A program is a sequence of assignments
newtype SBVPgm = SBVPgm {pgmAssignments :: S.Seq (SV, SBVExpr)}
               deriving G.Data

-- | Helper synonym for text, in case we switch to something else later.
type Name = T.Text

-- | 'NamedSymVar' pairs symbolic values and user given/automatically generated names
data NamedSymVar = NamedSymVar !SV !Name
                 deriving (Show, Generic, G.Data)

-- | For comparison purposes, we simply use the SV and ignore the name
instance Eq NamedSymVar where
  (==) (NamedSymVar l _) (NamedSymVar r _) = l == r

instance Ord NamedSymVar where
  compare (NamedSymVar l _) (NamedSymVar r _) = compare l r

-- | Convert to a named symvar, from string
toNamedSV' :: SV -> String -> NamedSymVar
toNamedSV' s = NamedSymVar s . T.pack

-- | Convert to a named symvar, from text
toNamedSV :: SV -> Name -> NamedSymVar
toNamedSV = NamedSymVar

-- | Get the node id from a named sym var
namedNodeId :: NamedSymVar -> NodeId
namedNodeId = swNodeId . getSV

-- | Get the SV from a named sym var
getSV :: NamedSymVar -> SV
getSV (NamedSymVar s _) = s

-- | Get the user-name typed value from named sym var
getUserName :: NamedSymVar -> Name
getUserName (NamedSymVar _ nm) = nm

-- | Get the string typed value from named sym var
getUserName' :: NamedSymVar -> String
getUserName' = T.unpack . getUserName

-- | Style of optimization. Note that in the pareto case the user is allowed
-- to specify a max number of fronts to query the solver for, since there might
-- potentially be an infinite number of them and there is no way to know exactly
-- how many ahead of time. If 'Nothing' is given, SBV will possibly loop forever
-- if the number is really infinite.
data OptimizeStyle = Lexicographic      -- ^ Objectives are optimized in the order given, earlier objectives have higher priority.
                   | Independent        -- ^ Each objective is optimized independently.
                   | Pareto (Maybe Int) -- ^ Objectives are optimized according to pareto front: That is, no objective can be made better without making some other worse.
                   deriving (Eq, Show)

-- | Penalty for a soft-assertion. The default penalty is @1@, with all soft-assertions belonging
-- to the same objective goal. A positive weight and an optional group can be provided by using
-- the 'Penalty' constructor.
data Penalty = DefaultPenalty                  -- ^ Default: Penalty of @1@ and no group attached
             | Penalty Rational (Maybe String) -- ^ Penalty with a weight and an optional group
             deriving Show

-- | Objective of optimization. We can minimize, maximize, or give a soft assertion with a penalty
-- for not satisfying it.
data Objective a = Minimize          String a         -- ^ Minimize this metric
                 | Maximize          String a         -- ^ Maximize this metric
                 | AssertWithPenalty String a Penalty -- ^ A soft assertion, with an associated penalty
                 deriving (Show, Functor)

-- | The name of the objective
objectiveName :: Objective a -> String
objectiveName (Minimize          s _)   = s
objectiveName (Maximize          s _)   = s
objectiveName (AssertWithPenalty s _ _) = s

-- | The state we keep track of as we interact with the solver
data QueryState = QueryState { queryAsk                 :: Maybe Int -> String -> IO String
                             , querySend                :: Maybe Int -> String -> IO ()
                             , queryRetrieveResponse    :: Maybe Int -> IO String
                             , queryConfig              :: SMTConfig
                             , queryTerminate           :: IO ()
                             , queryTimeOutValue        :: Maybe Int
                             , queryAssertionStackDepth :: Int
                             }

-- | Computations which support query operations.
class Monad m => MonadQuery m where
  queryState :: m State

  default queryState :: (MonadTrans t, MonadQuery m', m ~ t m') => m State
  queryState = lift queryState

instance MonadQuery m             => MonadQuery (ExceptT e m)
instance MonadQuery m             => MonadQuery (MaybeT m)
instance MonadQuery m             => MonadQuery (ReaderT r m)
instance MonadQuery m             => MonadQuery (SS.StateT s m)
instance MonadQuery m             => MonadQuery (LS.StateT s m)
instance (MonadQuery m, Monoid w) => MonadQuery (SW.WriterT w m)
instance (MonadQuery m, Monoid w) => MonadQuery (LW.WriterT w m)

-- | A query is a user-guided mechanism to directly communicate and extract
-- results from the solver. A generalization of 'Data.SBV.Query'.
newtype QueryT m a = QueryT { runQueryT :: ReaderT State m a }
    deriving (Applicative, Functor, Monad, MonadIO, MonadTrans,
              MonadError e, MonadState s, MonadWriter w)

instance Monad m => MonadQuery (QueryT m) where
  queryState = QueryT ask

mapQueryT :: (ReaderT State m a -> ReaderT State n b) -> QueryT m a -> QueryT n b
mapQueryT f = QueryT . f . runQueryT
{-# INLINE mapQueryT #-}

-- | Create a fresh variable of some type in the underlying query monad transformer.
-- For further control on how these variables are projected and embedded, see the
-- 'Queriable' class.
class Fresh m a where
  fresh :: QueryT m a

-- | An queriable value. This is a generalization of the 'Fresh' class, in case one needs
-- to be more specific about how projections/embeddings are done.
class Queriable m a where
  type QueryResult a :: Type

  -- | ^ Create a new symbolic value of type @a@
  create  :: QueryT m a

  -- | ^ Extract the current value in a SAT context
  project :: a -> QueryT m (QueryResult a)

  -- | ^ Create a literal value. Morally, 'embed' and 'project' are inverses of each other
  -- via the 'QueryT' monad transformer.
  embed   :: QueryResult a -> QueryT m a

-- Have to define this one by hand, because we use ReaderT in the implementation
instance MonadReader r m => MonadReader r (QueryT m) where
  ask = lift ask
  local f = mapQueryT $ mapReaderT $ local f

-- | A query is a user-guided mechanism to directly communicate and extract
-- results from the solver.
type Query = QueryT IO

instance MonadSymbolic Query where
   symbolicEnv = queryState

instance NFData OptimizeStyle where
   rnf x = x `seq` ()

instance NFData Penalty where
   rnf DefaultPenalty  = ()
   rnf (Penalty p mbs) = rnf p `seq` rnf mbs

instance NFData a => NFData (Objective a) where
   rnf (Minimize          s a)   = rnf s `seq` rnf a
   rnf (Maximize          s a)   = rnf s `seq` rnf a
   rnf (AssertWithPenalty s a p) = rnf s `seq` rnf a `seq` rnf p

-- | A result can either produce something at the top or as a lambda/constraint. Distinguish by inputs
data ResultInp = ResultTopInps ([NamedSymVar], [NamedSymVar])  -- user inputs -- trackers
               | ResultLamInps [(Quantifier, NamedSymVar)]     -- for constraints, we can have quantifiers
               deriving G.Data

instance NFData ResultInp where
   rnf (ResultTopInps xs) = rnf xs
   rnf (ResultLamInps xs) = rnf xs

-- | Several data about the program
data ProgInfo = ProgInfo { hasQuants         :: Bool
                         , progSpecialRels   :: [SpecialRelOp]
                         , progTransClosures :: [(String, String)]
                         }
                         deriving G.Data

instance NFData ProgInfo where
   rnf (ProgInfo a b c) = rnf a `seq` rnf b `seq` rnf c

deriving instance G.Data CallStack
deriving instance G.Data SrcLoc

-- | Result of running a symbolic computation
data Result = Result { progInfo       :: ProgInfo                                     -- ^ various info we collect about the program
                     , reskinds       :: Set.Set Kind                                 -- ^ kinds used in the program
                     , resTraces      :: [(String, CV)]                               -- ^ quick-check counter-example information (if any)
                     , resObservables :: [(String, CV -> Bool, SV)]                   -- ^ observable expressions (part of the model)
                     , resUISegs      :: [(String, [String])]                         -- ^ uninterpeted code segments
                     , resParams      :: ResultInp                                    -- ^ top-inputs or lambda params
                     , resConsts      :: (CnstMap, [(SV, CV)])                        -- ^ constants
                     , resTables      :: [((Int, Kind, Kind), [SV])]                  -- ^ tables (automatically constructed) (tableno, index-type, result-type) elts
                     , resArrays      :: [(Int, ArrayInfo)]                           -- ^ arrays (user specified)
                     , resUIConsts    :: [(String, (Bool, Maybe [String], SBVType))]  -- ^ uninterpreted constants
                     , resDefinitions :: [(SMTDef, SBVType)]                          -- ^ definitions created via smtFunction or lambda
                     , resAsgns       :: SBVPgm                                       -- ^ assignments
                     , resConstraints :: S.Seq (Bool, [(String, String)], SV)         -- ^ additional constraints (boolean)
                     , resAssertions  :: [(String, Maybe CallStack, SV)]              -- ^ assertions
                     , resOutputs     :: [SV]                                         -- ^ outputs
                     }
                     deriving G.Data

-- Show instance for 'Result'. Only for debugging purposes.
instance Show Result where
  -- If there's nothing interesting going on, just print the constant. Note that the
  -- definition of interesting here is rather subjective; but essentially if we reduced
  -- the result to a single constant already, without any reference to anything.
  show Result{resConsts=(_, cs), resOutputs=[r]}
    | Just c <- r `lookup` cs
    = show c
  show (Result _ kinds _ _ cgs params (_, cs) ts as uis defns xs cstrs asserts os) = intercalate "\n" $
                   (if null usorts then [] else "SORTS" : map ("  " ++) usorts)
                ++ (case params of
                      ResultTopInps (i, t) -> "INPUTS" : map shn i ++ (if null t then [] else "TRACKER VARS" : map shn t)
                      ResultLamInps qs     -> "LAMBDA-CONSTRAINT PARAMS" : map shq qs
                   )
                ++ ["CONSTANTS"]
                ++ concatMap shc cs
                ++ ["TABLES"]
                ++ map sht ts
                ++ ["ARRAYS"]
                ++ map sha as
                ++ ["UNINTERPRETED CONSTANTS"]
                ++ map shui uis
                ++ ["USER GIVEN CODE SEGMENTS"]
                ++ concatMap shcg cgs
                ++ ["AXIOMS-DEFINITIONS"]
                ++ map show defns
                ++ ["DEFINE"]
                ++ map (\(s, e) -> "  " ++ shs s ++ " = " ++ show e) (F.toList (pgmAssignments xs))
                ++ ["CONSTRAINTS"]
                ++ map (("  " ++) . shCstr) (F.toList cstrs)
                ++ ["ASSERTIONS"]
                ++ map (("  "++) . shAssert) asserts
                ++ ["OUTPUTS"]
                ++ sh2 os
    where sh2 :: Show a => [a] -> [String]
          sh2 = map (("  "++) . show)

          usorts = [sh s t | KUserSort s t <- Set.toList kinds]
                   where sh s Nothing   = s
                         sh s (Just es) = s ++ " (" ++ intercalate ", " es ++ ")"

          shs sv = show sv ++ " :: " ++ show (swKind sv)

          sht ((i, at, rt), es)  = "  Table " ++ show i ++ " : " ++ show at ++ "->" ++ show rt ++ " = " ++ show es

          shc (sv, cv)
            | sv == falseSV || sv == trueSV
            = []
            | True
            = ["  " ++ show sv ++ " = " ++ show cv]

          shcg (s, ss) = ("Variable: " ++ s) : map ("  " ++) ss

          shn (NamedSymVar sv nm) = "  " <> ni <> " :: " ++ show (swKind sv) ++ alias
            where ni = show sv

                  alias | ni == T.unpack nm = ""
                        | True              = ", aliasing " ++ show nm

          shq (q, v) = shn v ++ ", " ++ if q == ALL then "universal" else "existential"

          sha (i, (nm, (ai, bi), ctx)) = "  " ++ ni ++ " :: " ++ show ai ++ " -> " ++ show bi ++ alias
                                       ++ "\n     Context: "     ++ show ctx
            where ni = "array_" ++ show i
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm

          shui (nm, t) = "  [uninterpreted] " ++ nm ++ " :: " ++ show t

          shCstr (isSoft, [], c)               = soft isSoft ++ show c
          shCstr (isSoft, [(":named", nm)], c) = soft isSoft ++ nm ++ ": " ++ show c
          shCstr (isSoft, attrs, c)            = soft isSoft ++ show c ++ " (attributes: " ++ show attrs ++ ")"

          soft True  = "[SOFT] "
          soft False = ""

          shAssert (nm, stk, p) = "  -- assertion: " ++ nm ++ " " ++ maybe "[No location]"
#if MIN_VERSION_base(4,9,0)
                prettyCallStack
#else
                showCallStack
#endif
                stk ++ ": " ++ show p

-- | The context of a symbolic array as created
data ArrayContext = ArrayFree   (Either (Maybe SV) String) -- ^ A new array, the contents are initialized with the given value, if any, or the custom lambda given
                  | ArrayMutate ArrayIndex SV SV           -- ^ An array created by mutating another array at a given cell
                  | ArrayMerge  SV ArrayIndex ArrayIndex   -- ^ An array created by symbolically merging two other arrays
                  deriving G.Data

instance Show ArrayContext where
  show (ArrayFree (Left Nothing))   = " initialized with random elements"
  show (ArrayFree (Left (Just sv))) = " initialized with " ++ show sv
  show (ArrayFree (Right lambda))   = " initialized with " ++ show lambda
  show (ArrayMutate i a b)   = " cloned from array_" ++ show i ++ " with " ++ show a ++ " :: " ++ show (swKind a) ++ " |-> " ++ show b ++ " :: " ++ show (swKind b)
  show (ArrayMerge  s i j)   = " merged arrays " ++ show i ++ " and " ++ show j ++ " on condition " ++ show s

-- | Expression map, used for hash-consing
type ExprMap = Map.Map SBVExpr SV

-- | Constants are stored in a map, for hash-consing.
type CnstMap = Map.Map CV SV

-- | Kinds used in the program; used for determining the final SMT-Lib logic to pick
type KindSet = Set.Set Kind

-- | Tables generated during a symbolic run
type TableMap = Map.Map (Kind, Kind, [SV]) Int

-- | Representation for symbolic arrays
type ArrayInfo = (String, (Kind, Kind), ArrayContext)

-- | SMT Arrays generated during a symbolic run
type ArrayMap = IMap.IntMap ArrayInfo

-- | Uninterpreted-constants generated during a symbolic run
type UIMap = Map.Map String (Bool, Maybe [String], SBVType)   -- If Bool is true, then this is a curried function

-- | Code-segments for Uninterpreted-constants, as given by the user
type CgMap = Map.Map String [String]

-- | Cached values, implementing sharing
type Cache a = IMap.IntMap [(StableName (State -> IO a), a)]

-- | Stage of an interactive run
data IStage = ISetup        -- Before we initiate contact.
            | ISafe         -- In the context of a safe/safeWith call
            | IRun          -- After the contact is started

-- | Are we checking safety
isSafetyCheckingIStage :: IStage -> Bool
isSafetyCheckingIStage s = case s of
                             ISetup -> False
                             ISafe  -> True
                             IRun   -> False

-- | Are we in setup?
isSetupIStage :: IStage -> Bool
isSetupIStage s = case s of
                   ISetup -> True
                   ISafe  -> False
                   IRun   -> True

-- | Are we in a run?
isRunIStage :: IStage -> Bool
isRunIStage s = case s of
                  ISetup -> False
                  ISafe  -> False
                  IRun   -> True

-- | Different means of running a symbolic piece of code
data SBVRunMode = SMTMode QueryContext IStage Bool SMTConfig   -- ^ In regular mode, with a stage. Bool is True if this is SAT.
                | CodeGen                                      -- ^ Code generation mode.
                | LambdaGen Int                                -- ^ Inside a lambda-expression at level
                | Concrete (Maybe (Bool, [(NamedSymVar, CV)])) -- ^ Concrete simulation mode, with given environment if any. If Nothing: Random.

-- Show instance for SBVRunMode; debugging purposes only
instance Show SBVRunMode where
   show (SMTMode qc ISetup True  _)  = "Satisfiability setup (" ++ show qc ++ ")"
   show (SMTMode qc ISafe  True  _)  = "Safety setup (" ++ show qc ++ ")"
   show (SMTMode qc IRun   True  _)  = "Satisfiability (" ++ show qc ++ ")"
   show (SMTMode qc ISetup False _)  = "Proof setup (" ++ show qc ++ ")"
   show (SMTMode qc ISafe  False _)  = error $ "ISafe-False is not an expected/supported combination for SBVRunMode! (" ++ show qc ++ ")"
   show (SMTMode qc IRun   False _)  = "Proof (" ++ show qc ++ ")"
   show CodeGen                      = "Code generation"
   show LambdaGen{}                  = "Lambda generation"
   show (Concrete Nothing)           = "Concrete evaluation with random values"
   show (Concrete (Just (True, _)))  = "Concrete evaluation during model validation for sat"
   show (Concrete (Just (False, _))) = "Concrete evaluation during model validation for prove"

-- | Is this a CodeGen run? (i.e., generating code)
isCodeGenMode :: State -> IO Bool
isCodeGenMode State{runMode} = do rm <- readIORef runMode
                                  return $ case rm of
                                             Concrete{}  -> False
                                             SMTMode{}   -> False
                                             LambdaGen{} -> False
                                             CodeGen     -> True

-- | The state in query mode, i.e., additional context
data IncState = IncState { rNewInps        :: IORef [NamedSymVar]   -- always existential!
                         , rNewKinds       :: IORef KindSet
                         , rNewConsts      :: IORef CnstMap
                         , rNewArrs        :: IORef ArrayMap
                         , rNewTbls        :: IORef TableMap
                         , rNewUIs         :: IORef UIMap
                         , rNewAsgns       :: IORef SBVPgm
                         , rNewConstraints :: IORef (S.Seq (Bool, [(String, String)], SV))
                         }

-- | Get a new IncState
newIncState :: IO IncState
newIncState = do
        is    <- newIORef []
        ks    <- newIORef Set.empty
        nc    <- newIORef Map.empty
        am    <- newIORef IMap.empty
        tm    <- newIORef Map.empty
        ui    <- newIORef Map.empty
        pgm   <- newIORef (SBVPgm S.empty)
        cstrs <- newIORef S.empty
        return IncState { rNewInps        = is
                        , rNewKinds       = ks
                        , rNewConsts      = nc
                        , rNewArrs        = am
                        , rNewTbls        = tm
                        , rNewUIs         = ui
                        , rNewAsgns       = pgm
                        , rNewConstraints = cstrs
                        }

-- | Get a new IncState
withNewIncState :: State -> (State -> IO a) -> IO (IncState, a)
withNewIncState st cont = do
        is <- newIncState
        R.modifyIORef' (rIncState st) (const is)
        r  <- cont st
        finalIncState <- readIORef (rIncState st)
        return (finalIncState, r)

-- | User defined inputs
type UserInputs = S.Seq NamedSymVar

-- | Internally declared
type InternInps = S.Seq NamedSymVar

-- | Entire set of names, for faster lookup
type AllInps = Set.Set Name

-- | Inputs as a record of maps and sets. See above type-synonyms for their roles.
data Inputs = Inputs { userInputs   :: !UserInputs
                     , internInputs :: !InternInps
                     , allInputs    :: !AllInps
                     } deriving (Eq,Show)

-- | Inputs to a lambda-abstraction. These are quantified to handle constraints
type LambdaInputs = S.Seq (Quantifier, NamedSymVar)

-- | Semigroup instance; combining according to indexes.
instance Semigroup Inputs where
  (Inputs lui lii lai) <> (Inputs rui rii rai) = Inputs (lui <> rui) (lii <> rii) (lai <> rai)

-- | Monoid instance, we start with no maps.
instance Monoid Inputs where
  mempty = Inputs { userInputs   = mempty
                  , internInputs = mempty
                  , allInputs    = mempty
                  }

-- | Modify the user-inputs field
onUserInputs :: (UserInputs -> UserInputs) -> Inputs -> Inputs
onUserInputs f inp@Inputs{userInputs} = inp{userInputs = f userInputs}

-- | Modify the internal-inputs field
onInternInputs :: (InternInps -> InternInps) -> Inputs -> Inputs
onInternInputs f inp@Inputs{internInputs} = inp{internInputs = f internInputs}

-- | Modify the all-inputs field
onAllInputs :: (AllInps -> AllInps) -> Inputs -> Inputs
onAllInputs f inp@Inputs{allInputs} = inp{allInputs = f allInputs}

-- | Add a new internal input
addInternInput :: SV -> Name -> Inputs -> Inputs
addInternInput sv nm = goAll . goIntern
  where !new = toNamedSV sv nm
        goIntern = onInternInputs (S.|> new)
        goAll    = onAllInputs    (Set.insert nm)

-- | Add a new user input
addUserInput :: SV -> Name -> Inputs -> Inputs
addUserInput sv nm = goAll . goUser
  where new    = toNamedSV sv nm
        goUser = onUserInputs (S.|> new)        -- add to the end of the sequence
        goAll  = onAllInputs  (Set.insert nm)

-- | Find a user-input from its SV. Note that only level-0 vars
-- can be found this way.
lookupInput :: Eq a => (a -> SV) -> SV -> S.Seq a -> Maybe a
lookupInput f sv ns
   | l == 0 = res
   | True   = Nothing  -- l != 0, a lambda var, so we ignore
  where
    (_, l, i) = getId (swNodeId sv)
    svs       = fmap f ns
    res       = case S.lookup i ns of -- Nothing on negative Int or Int > length seq
                  Nothing    -> secondLookup
                  x@(Just e) -> if sv == f e then x else secondLookup
                    -- we try the fast lookup first, if the node ids don't match then
                    -- we use the more expensive O (n) to find the index and the elem
    secondLookup = S.elemIndexL sv svs >>= flip S.lookup ns

-- | A defined function/value
data SMTDef = SMTDef String           -- ^ Defined functions -- name
                     Kind             -- ^ Final kind of the definition (resulting kind, not the params)
                     [String]         -- ^ other definitions it refers to
                     (Maybe String)   -- ^ parameter string
                     (Int -> String)  -- ^ Body, in SMTLib syntax, given the tab amount
            | SMTLam Kind             -- ^ Final kind of the definition (resulting kind, not the params)
                     [String]         -- ^ Anonymous function -- other definitions it refers to
                     (Maybe String)   -- ^ parameter string
                     (Int -> String)  -- ^ Body, in SMTLib syntax, given the tab amount
            deriving G.Data

-- | For debug purposes
instance Show SMTDef where
  show d = case d of
             SMTDef nm fk frees p body -> shDef (Just nm) fk frees p body
             SMTLam    fk frees p body -> shDef Nothing   fk frees p body
    where shDef mbNm fk frees p body = unlines [ "-- User defined function: " ++ fromMaybe "Anonymous" mbNm
                                               , "-- Final return type    : " ++ show fk
                                               , "-- Refers to            : " ++ intercalate ", " frees
                                               , "-- Parameters           : " ++ fromMaybe "NONE" p
                                               , "-- Body                 : "
                                               , body 2
                                               ]

-- The name of this definition
smtDefGivenName :: SMTDef -> Maybe String
smtDefGivenName (SMTDef n _ _ _ _) = Just n
smtDefGivenName SMTLam{}           = Nothing

-- | NFData instance for SMTDef
instance NFData SMTDef where
  rnf (SMTDef n fk frees params body) = rnf n `seq` rnf fk `seq` rnf frees `seq` rnf params `seq` rnf body
  rnf (SMTLam   fk frees params body) =             rnf fk `seq` rnf frees `seq` rnf params `seq` rnf body

-- | The state of the symbolic interpreter
data State  = State { sbvContext          :: SBVContext
                    , pathCond            :: SVal                             -- ^ kind KBool
                    , stCfg               :: SMTConfig
                    , startTime           :: UTCTime
                    , rProgInfo           :: IORef ProgInfo
                    , runMode             :: IORef SBVRunMode
                    , rIncState           :: IORef IncState
                    , rCInfo              :: IORef [(String, CV)]
                    , rObservables        :: IORef (S.Seq (Name, CV -> Bool, SV))
                    , rctr                :: IORef Int
                    , rLambdaLevel        :: IORef Int
                    , rUsedKinds          :: IORef KindSet
                    , rUsedLbls           :: IORef (Set.Set String)
                    , rinps               :: IORef Inputs
                    , rlambdaInps         :: IORef LambdaInputs
                    , rConstraints        :: IORef (S.Seq (Bool, [(String, String)], SV))
                    , rPartitionVars      :: IORef [String]
                    , routs               :: IORef [SV]
                    , rtblMap             :: IORef TableMap
                    , spgm                :: IORef SBVPgm
                    , rconstMap           :: IORef CnstMap
                    , rexprMap            :: IORef ExprMap
                    , rArrayMap           :: IORef ArrayMap
                    , rUIMap              :: IORef UIMap
                    , rUserFuncs          :: IORef (Set.Set String) -- Functions that the user wanted explicit code generation for
                    , rCgMap              :: IORef CgMap
                    , rDefns              :: IORef [(SMTDef, SBVType)]
                    , rSMTOptions         :: IORef [SMTOption]
                    , rOptGoals           :: IORef [Objective (SV, SV)]
                    , rAsserts            :: IORef [(String, Maybe CallStack, SV)]
                    , rOutstandingAsserts :: IORef Bool            -- Did we send an assert after the last check-sat call?
                    , rSVCache            :: IORef (Cache SV)
                    , rAICache            :: IORef (Cache ArrayIndex)
                    , rQueryState         :: IORef (Maybe QueryState)
                    , parentState         :: Maybe State  -- Pointer to our parent if we're in a sublevel
                    }

-- | Chase to the root state. No infinite chains!
getRootState :: State -> State
getRootState st = maybe st getRootState (parentState st)

-- NFData is a bit of a lie, but it's sufficient, most of the content is iorefs that we don't want to touch
instance NFData State where
   rnf State{} = ()

-- | Get the current path condition
getSValPathCondition :: State -> SVal
getSValPathCondition = pathCond

-- | Extend the path condition with the given test value.
extendSValPathCondition :: State -> (SVal -> SVal) -> State
extendSValPathCondition st f = st{pathCond = f (pathCond st)}

-- | Are we running in proof mode?
inSMTMode :: State -> IO Bool
inSMTMode State{runMode} = do rm <- readIORef runMode
                              return $ case rm of
                                         CodeGen     -> False
                                         LambdaGen{} -> False
                                         Concrete{}  -> False
                                         SMTMode{}   -> True

-- | The "Symbolic" value. Either a constant (@Left@) or a symbolic
-- value (@Right Cached@). Note that caching is essential for making
-- sure sharing is preserved.
data SVal = SVal !Kind !(Either CV (Cached SV))

instance HasKind SVal where
  kindOf (SVal k _) = k

-- Show instance for 'SVal'. Not particularly "desirable", but will do if needed
-- NB. We do not show the type info on constant KBool values, since there's no
-- implicit "fromBoolean" applied to Booleans in Haskell; and thus a statement
-- of the form "True :: SBool" is just meaningless. (There should be a fromBoolean!)
instance Show SVal where
  show (SVal KBool (Left c))  = showCV False c
  show (SVal k     (Left c))  = showCV False c ++ " :: " ++ show k
  show (SVal k     (Right _)) =         "<symbolic> :: " ++ show k

-- | This instance is only defined so that we can define an instance for
-- 'Data.Bits.Bits'. '==' and '/=' simply throw an error.
-- We really don't want an 'Eq' instance for 'Data.SBV.Core.SBV' or 'SVal'. As it really makes no sense.
-- But since we do want the 'Data.Bits.Bits' instance, we're forced to define equality. See
-- <http://github.com/LeventErkok/sbv/issues/301>. We simply error out.
instance Eq SVal where
  a == b = noEquals "==" ".==" (show a, show b)
  a /= b = noEquals "/=" "./=" (show a, show b)

-- Bail out nicely.
noEquals :: String -> String -> (String, String) -> a
noEquals o n (l, r) = error $ unlines [ ""
                                      , "*** Data.SBV: Comparing symbolic values using Haskell's Eq class!"
                                      , "***"
                                      , "*** Received:    " ++ l ++ "  " ++ o ++ " " ++ r
                                      , "*** Instead use: " ++ l ++ " "  ++ n ++ " " ++ r
                                      , "***"
                                      , "*** The Eq instance for symbolic values are necessiated only because"
                                      , "*** of the Bits class requirement. You must use symbolic equality"
                                      , "*** operators instead. (And complain to Haskell folks that they"
                                      , "*** remove the 'Eq' superclass from 'Bits'!.)"
                                      ]

-- | Things we do not support in interactive mode, at least for now!
noInteractive :: [String] -> a
noInteractive ss = error $ unlines $  ""
                                   :  "*** Data.SBV: Unsupported interactive/query mode feature."
                                   :  map ("***  " ++) ss
                                   ++ ["*** Data.SBV: Please report this as a feature request!"]

-- | Things we do not support in interactive mode, nor we ever intend to
noInteractiveEver :: [String] -> a
noInteractiveEver ss = error $ unlines $  ""
                                       :  "*** Data.SBV: Unsupported interactive/query mode feature."
                                       :  map ("***  " ++) ss

-- | Modification of the state, but carefully handling the interactive tasks.
-- Note that the state is always updated regardless of the mode, but we get
-- to also perform extra operation in interactive mode. (Typically error out, but also simply
-- ignore if it has no impact.)
modifyState :: State -> (State -> IORef a) -> (a -> a) -> IO () -> IO ()
modifyState st@State{runMode} field update interactiveUpdate = do
        R.modifyIORef' (field st) update
        rm <- readIORef runMode
        case rm of
          SMTMode _ IRun _ _ -> interactiveUpdate
          _                  -> return ()

-- | Modify the incremental state
modifyIncState  :: State -> (IncState -> IORef a) -> (a -> a) -> IO ()
modifyIncState State{rIncState} field update = do
        incState <- readIORef rIncState
        R.modifyIORef' (field incState) update

-- | Add an observable
-- notice that we cons like a list, we should build at the end of the seq, but cons to preserve semantics for now
recordObservable :: State -> String -> (CV -> Bool) -> SV -> IO ()
recordObservable st (T.pack -> nm) chk sv = modifyState st rObservables ((nm, chk, sv) S.<|) (return ())

-- | Increment the variable counter
incrementInternalCounter :: State -> IO Int
incrementInternalCounter st = do ctr <- readIORef (rctr st)
                                 modifyState st rctr (+1) (return ())
                                 return ctr
{-# INLINE incrementInternalCounter #-}

-- | Kind of code we have for uninterpretation
data UICodeKind = UINone Bool     -- no code. If bool is true, then curried.
                | UISMT  SMTDef   -- SMTLib, first argument are the free-variables in it
                | UICgC  [String] -- Code-gen, currently only C

-- | Uninterpreted constants and functions. An uninterpreted constant is
-- a value that is indexed by its name. The only property the prover assumes
-- about these values are that they are equivalent to themselves; i.e., (for
-- functions) they return the same results when applied to same arguments.
-- We support uninterpreted-functions as a general means of black-box'ing
-- operations that are /irrelevant/ for the purposes of the proof; i.e., when
-- the proofs can be performed without any knowledge about the function itself.
svUninterpreted :: Kind -> String -> UICodeKind -> [SVal] -> SVal
svUninterpreted k nm code args = svUninterpretedGen k nm code args Nothing

svUninterpretedNamedArgs :: Kind -> String -> UICodeKind -> [(SVal, String)] -> SVal
svUninterpretedNamedArgs k nm code args = svUninterpretedGen k nm code (map fst args) (Just (map snd args))

svUninterpretedGen :: Kind -> String -> UICodeKind -> [SVal] -> Maybe [String] -> SVal
svUninterpretedGen k nm code args mbArgNames = SVal k $ Right $ cache result
  where result st = do let ty = SBVType (map kindOf args ++ [k])
                       newUninterpreted st (nm, mbArgNames) ty code
                       sws <- mapM (svToSV st) args
                       mapM_ forceSVArg sws
                       newExpr st k $ SBVApp (Uninterpreted nm) sws

-- | Create a new uninterpreted symbol, possibly with user given code
newUninterpreted :: State -> (String, Maybe [String]) -> SBVType -> UICodeKind -> IO ()
newUninterpreted st (nm, mbArgNames) t uiCode
  | not (isInternal || case nm of
                         []   -> False
                         h:tl -> enclosed || (isAlpha h && all validChar tl))
  = error $ "Bad uninterpreted constant name: " ++ show nm ++ ". Must be a valid SMTLib identifier."
  | True
  = do uiMap <- readIORef (rUIMap st)

       isCurried <- case uiCode of
                      UINone c -> pure c
                      UISMT d  -> do modifyState st rDefns (\defs -> (d, t) : filter (\(o, _) -> smtDefGivenName o /= Just nm) defs)
                                       $ noInteractive [ "Defined functions (smtFunction):"
                                                       , "  Name: " ++ nm
                                                       , "  Type: " ++ show t
                                                       , ""
                                                       , "You should use these functions at least once the query part starts"
                                                       , "and then use them in the query section as usual."
                                                       ]
                                     pure True
                      UICgC c  -> -- No need to record the code in interactive mode: CodeGen doesn't use interactive
                                  do modifyState st rCgMap (Map.insert nm c) (return ())
                                     pure True

       case nm `Map.lookup` uiMap of
         Just (_, _, t') -> checkType t' (return ())
         Nothing         -> modifyState st rUIMap (Map.insert nm (isCurried, mbArgNames, t))
                              $ modifyIncState st rNewUIs
                                                 (\newUIs -> case nm `Map.lookup` newUIs of
                                                               Just (_, _, t') -> checkType t' newUIs
                                                               Nothing         -> Map.insert nm (isCurried, mbArgNames, t) newUIs)
  where checkType :: SBVType -> r -> r
        checkType t' cont
          | t /= t' = error $  "Uninterpreted constant " ++ show nm ++ " used at incompatible types\n"
                            ++ "      Current type      : " ++ show t ++ "\n"
                            ++ "      Previously used at: " ++ show t'
          | True    = cont

        validChar x = isAlphaNum x || x `elem` ("_" :: String)
        enclosed    =  "|" `isPrefixOf` nm
                    && "|" `isSuffixOf` nm
                    && length nm > 2
                    && not (any (`elem` ("|\\" :: String)) (drop 1 (init nm)))

        -- let internal names go through
        isInternal = "__internal_sbv_" `isPrefixOf` nm

-- | Add a new sAssert based constraint
addAssertion :: State -> Maybe CallStack -> String -> SV -> IO ()
addAssertion st cs msg cond = modifyState st rAsserts ((msg, cs, cond):)
                                        $ noInteractive [ "Named assertions (sAssert):"
                                                        , "  Tag: " ++ msg
                                                        , "  Loc: " ++ maybe "Unknown" show cs
                                                        ]

-- | Create an internal variable, which acts as an input but isn't visible to the user.
-- Such variables are existentially quantified in a SAT context, and universally quantified
-- in a proof context.
internalVariable :: State -> Kind -> IO SV
internalVariable st k = do NamedSymVar sv nm <- newSV st k
                           let n = "__internal_sbv_" <> nm
                               v = NamedSymVar sv n
                           modifyState st rinps (addUserInput sv n) $ modifyIncState st rNewInps (v :)
                           return sv
{-# INLINE internalVariable #-}

-- | Create a variable to be used in a constraint-expression
quantVar :: Quantifier -> State -> Kind -> IO SV
quantVar q st k = do v@(NamedSymVar sv _) <- newSV st k
                     modifyState st rlambdaInps (S.|> (q, v)) (return ())
                     return sv
{-# INLINE quantVar #-}

-- | Create a variable to be used in a lambda-expression
lambdaVar :: State -> Kind -> IO SV
lambdaVar = quantVar ALL
{-# INLINE lambdaVar #-}

-- | Create a new SV
newSV :: State -> Kind -> IO NamedSymVar
newSV st k = do ctr <- incrementInternalCounter st
                ll  <- readIORef (rLambdaLevel st)
                let sv = SV k (NodeId (sbvContext st, ll, ctr))
                registerKind st k
                return $ NamedSymVar sv $ T.pack (show sv)
{-# INLINE newSV #-}

-- | Register a new kind with the system, used for uninterpreted sorts.
-- NB: Is it safe to have new kinds in query mode? It could be that
-- the new kind might introduce a constraint that effects the logic. For
-- instance, if we're seeing 'Double' for the first time and using a BV
-- logic, then things would fall apart. But this should be rare, and hopefully
-- the success-response checking mechanism will catch the rare cases where this
-- is an issue. In either case, the user can always arrange for the right
-- logic by calling 'Data.SBV.setLogic' appropriately, so it seems safe to just
-- allow for this.
registerKind :: State -> Kind -> IO ()
registerKind st k
  | KUserSort sortName _ <- k, map toLower sortName `elem` smtLibReservedNames
  = error $ "SBV: " ++ show sortName ++ " is a reserved sort; please use a different name."
  | True
  = do -- Adding a kind to the incState is tricky; we only need to add it
       --     *    If it's an uninterpreted sort that's not already in the general state
       --     * OR If it's a tuple-sort whose cardinality isn't already in the general state
       --     * OR If it's a list that's not already in the general state (so we can send the flatten commands)

       existingKinds <- readIORef (rUsedKinds st)

       modifyState st rUsedKinds (Set.insert k) $ do

                          -- Why do we discriminate here? Because the incremental context is sensitive to the
                          -- order: In particular, if an uninterpreted kind is already in there, we don't
                          -- want to re-add because double-declaration would be wrong. See 'cvtInc' for details.
                          let needsAdding = case k of
                                              KUserSort{} -> k `notElem` existingKinds
                                              KList{}     -> k `notElem` existingKinds
                                              KTuple nks  -> length nks `notElem` [length oks | KTuple oks <- Set.toList existingKinds]
                                              KMaybe{}    -> k `notElem` existingKinds
                                              KEither{}   -> k `notElem` existingKinds
                                              _           -> False

                          when needsAdding $ modifyIncState st rNewKinds (Set.insert k)

       -- Don't forget to register subkinds!
       case k of
         KBool     {}    -> return ()
         KBounded  {}    -> return ()
         KUnbounded{}    -> return ()
         KReal     {}    -> return ()
         KUserSort {}    -> return ()
         KFloat    {}    -> return ()
         KDouble   {}    -> return ()
         KFP       {}    -> return ()
         KRational {}    -> return ()
         KChar     {}    -> return ()
         KString   {}    -> return ()
         KList     ek    -> registerKind st ek
         KSet      ek    -> registerKind st ek
         KTuple    eks   -> mapM_ (registerKind st) eks
         KMaybe    ke    -> registerKind st ke
         KEither   k1 k2 -> mapM_ (registerKind st) [k1, k2]

-- | Register a new label with the system, making sure they are unique and have no '|'s in them
registerLabel :: String -> State -> String -> IO ()
registerLabel whence st nm
  | map toLower nm `elem` smtLibReservedNames
  = err "is a reserved string; please use a different name."
  | '|' `elem` nm
  = err "contains the character `|', which is not allowed!"
  | '\\' `elem` nm
  = err "contains the character `\\', which is not allowed!"
  | True
  = do old <- readIORef $ rUsedLbls st
       if nm `Set.member` old
          then err "is used multiple times. Please do not use duplicate names!"
          else modifyState st rUsedLbls (Set.insert nm) (return ())

  where err w = error $ "SBV (" ++ whence ++ "): " ++ show nm ++ " " ++ w

-- | Create a new constant; hash-cons as necessary
newConst :: State -> CV -> IO SV
newConst st c = do
  constMap <- readIORef (rconstMap st)
  case c `Map.lookup` constMap of
    -- NB. Unlike in 'newExpr', we don't have to make sure the returned sv
    -- has the kind we asked for, because the constMap stores the full CV
    -- which already has a kind field in it.
    Just sv -> return sv
    Nothing -> do (NamedSymVar sv _) <- newSV st (kindOf c)
                  let ins = Map.insert c sv
                  modifyState st rconstMap ins $ modifyIncState st rNewConsts ins
                  return sv
{-# INLINE newConst #-}

-- | Create a new table; hash-cons as necessary
getTableIndex :: State -> Kind -> Kind -> [SV] -> IO Int
getTableIndex st at rt elts = do
  let key = (at, rt, elts)
  tblMap <- readIORef (rtblMap st)
  case key `Map.lookup` tblMap of
    Just i -> return i
    _      -> do let i   = Map.size tblMap
                     upd = Map.insert key i
                 modifyState st rtblMap upd $ modifyIncState st rNewTbls upd
                 return i

-- | Create a new expression; hash-cons as necessary
newExpr :: State -> Kind -> SBVExpr -> IO SV
newExpr st k app = do
   let e = reorder app
   exprMap <- readIORef (rexprMap st)
   case e `Map.lookup` exprMap of
     -- NB. Check to make sure that the kind of the hash-consed value
     -- is the same kind as we're requesting. This might look unnecessary,
     -- at first, but `svSign` and `svUnsign` rely on this as we can
     -- get the same expression but at a different type. See
     -- <http://github.com/GaloisInc/cryptol/issues/566> as an example.
     Just sv | kindOf sv == k -> return sv
     _                        -> do (NamedSymVar sv _) <- newSV st k
                                    checkConsistent sv e
                                    let append (SBVPgm xs) = SBVPgm (xs S.|> (sv, e))
                                    modifyState st spgm append $ modifyIncState st rNewAsgns append
                                    modifyState st rexprMap (Map.insert e sv) (return ())
                                    return sv
{-# INLINE newExpr #-}

-- | In rare cases, we can get a context mismatch; so make sure the expression is well-formed.
-- This isn't a full solution, but handles the common case (hopefully!)
checkConsistent :: SV -> SBVExpr -> IO ()
checkConsistent lhs (SBVApp _ args) = mapM_ check args
   where SV _ (NodeId (lhsContext, lambdaLevel, lhsId)) = lhs
         check (SV _ (NodeId (rhsContext, ll, ni)))
           | lhsContext `compatibleContext` rhsContext && lambdaLevel >= ll && (lambdaLevel /= ll || lhsId > ni)
           = pure ()
           | True
           = contextMismatchError lhsContext rhsContext (Just (lambdaLevel, lhsId)) (Just (ll, ni))
{-# INLINE checkConsistent #-}

-- | Are these compatible contexts? Either the same, or one of them is global
compatibleContext :: SBVContext -> SBVContext -> Bool
compatibleContext c1 c2 = c1 == c2 || c1 == globalSBVContext || c2 == globalSBVContext
{-# INLINE compatibleContext #-}

-- | Same as checkConsistent above, except in an array context
checkCompatibleContext :: SBVContext -> SBVContext -> IO ()
checkCompatibleContext ctx1 ctx2
   | ctx1 `compatibleContext` ctx2
   = pure ()
   | True
   = contextMismatchError ctx1 ctx2 Nothing Nothing
{-# INLINE checkCompatibleContext #-}

-- | Convert a symbolic value to an internal SV
svToSV :: State -> SVal -> IO SV
svToSV st (SVal _ (Left c))  = newConst st c
svToSV st (SVal _ (Right f)) = uncache f st

-- | Generalization of 'Data.SBV.svToSymSV'
svToSymSV :: MonadSymbolic m => SVal -> m SV
svToSymSV sbv = do st <- symbolicEnv
                   liftIO $ svToSV st sbv

-------------------------------------------------------------------------
-- * Symbolic Computations
-------------------------------------------------------------------------
-- | A Symbolic computation. Represented by a reader monad carrying the
-- state of the computation, layered on top of IO for creating unique
-- references to hold onto intermediate results.

-- | Computations which support symbolic operations
class MonadIO m => MonadSymbolic m where
  symbolicEnv :: m State

  default symbolicEnv :: (MonadTrans t, MonadSymbolic m', m ~ t m') => m State
  symbolicEnv = lift symbolicEnv

instance MonadSymbolic m             => MonadSymbolic (ExceptT e m)
instance MonadSymbolic m             => MonadSymbolic (MaybeT m)
instance MonadSymbolic m             => MonadSymbolic (ReaderT r m)
instance MonadSymbolic m             => MonadSymbolic (SS.StateT s m)
instance MonadSymbolic m             => MonadSymbolic (LS.StateT s m)
instance (MonadSymbolic m, Monoid w) => MonadSymbolic (SW.WriterT w m)
instance (MonadSymbolic m, Monoid w) => MonadSymbolic (LW.WriterT w m)

-- | A generalization of 'Data.SBV.Symbolic'.
newtype SymbolicT m a = SymbolicT { runSymbolicT :: ReaderT State m a }
                   deriving ( Applicative, Functor, Monad, MonadIO, MonadTrans
                            , MonadError e, MonadState s, MonadWriter w
#if MIN_VERSION_base(4,11,0)
                            , Fail.MonadFail
#endif
                            )

-- | `MonadSymbolic` instance for `SymbolicT m`
instance MonadIO m => MonadSymbolic (SymbolicT m) where
  symbolicEnv = SymbolicT ask

-- | Map a computation over the symbolic transformer.
mapSymbolicT :: (ReaderT State m a -> ReaderT State n b) -> SymbolicT m a -> SymbolicT n b
mapSymbolicT f = SymbolicT . f . runSymbolicT
{-# INLINE mapSymbolicT #-}

-- Have to define this one by hand, because we use ReaderT in the implementation
instance MonadReader r m => MonadReader r (SymbolicT m) where
  ask = lift ask
  local f = mapSymbolicT $ mapReaderT $ local f

-- | `Symbolic` is specialization of `SymbolicT` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Symbolic = SymbolicT IO

-- | Create a symbolic value, based on the quantifier we have. If an
-- explicit quantifier is given, we just use that. If not, then we
-- pick the quantifier appropriately based on the run-mode.
-- @randomCV@ is used for generating random values for this variable
-- when used for @quickCheck@ or 'Data.SBV.Tools.GenTest.genTest' purposes.
svMkSymVar :: VarContext -> Kind -> Maybe String -> State -> IO SVal
svMkSymVar = svMkSymVarGen False

-- | Create an existentially quantified tracker variable
svMkTrackerVar :: Kind -> String -> State -> IO SVal
svMkTrackerVar k nm = svMkSymVarGen True (NonQueryVar (Just EX)) k (Just nm)

-- | Generalization of 'Data.SBV.sWordN'
sWordN :: MonadSymbolic m => Int -> String -> m SVal
sWordN w nm = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar Nothing) (KBounded False w) (Just nm)

-- | Generalization of 'Data.SBV.sWordN_'
sWordN_ :: MonadSymbolic m => Int -> m SVal
sWordN_ w = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar Nothing) (KBounded False w) Nothing

-- | Generalization of 'Data.SBV.sIntN'
sIntN :: MonadSymbolic m => Int -> String -> m SVal
sIntN w nm = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar Nothing) (KBounded True w) (Just nm)

-- | Generalization of 'Data.SBV.sIntN_'
sIntN_ :: MonadSymbolic m => Int -> m SVal
sIntN_ w = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar Nothing) (KBounded True w) Nothing

-- | Create a symbolic value, based on the quantifier we have. If an
-- explicit quantifier is given, we just use that. If not, then we
-- pick the quantifier appropriately based on the run-mode.
-- @randomCV@ is used for generating random values for this variable
-- when used for @quickCheck@ or 'Data.SBV.Tools.GenTest.genTest' purposes.
svMkSymVarGen :: Bool -> VarContext -> Kind -> Maybe String -> State -> IO SVal
svMkSymVarGen isTracker varContext k mbNm st = do
        rm <- readIORef (runMode st)

        let varInfo = case mbNm of
                        Nothing -> ", of type " ++ show k
                        Just nm -> ", while defining " ++ nm ++ " :: " ++ show k

            disallow what  = error $ "Data.SBV: Unsupported: " ++ what ++ varInfo ++ " in mode: " ++ show rm

            noUI cont
              | isUserSort k  = disallow "User defined sorts"
              | True          = cont

            (isQueryVar, mbQ) = case varContext of
                                  NonQueryVar mq -> (False, mq)
                                  QueryVar       -> (True,  Just EX)

            mkS q = do (NamedSymVar sv internalName) <- newSV st k
                       let nm = fromMaybe (T.unpack internalName) mbNm
                       introduceUserName st (isQueryVar, isTracker) nm k q sv

            mkC cv = do registerKind st k
                        modifyState st rCInfo ((fromMaybe "_" mbNm, cv):) (return ())
                        return $ SVal k (Left cv)

        case (mbQ, rm) of
          (Just q,  SMTMode{}          ) -> mkS q
          (Nothing, SMTMode _ _ isSAT _) -> mkS (if isSAT then EX else ALL)

          (Just EX, CodeGen{})           -> disallow "Existentially quantified variables"
          (_      , CodeGen)             -> noUI $ mkS ALL  -- code generation, pick universal

          (Just EX, Concrete Nothing)    -> disallow "Existentially quantified variables"
          (_      , Concrete Nothing)    -> noUI (randomCV k >>= mkC)

          (Just EX, LambdaGen{})         -> disallow "Existentially quantified variables"
          (_,       LambdaGen{})         -> noUI $ mkS ALL

          -- Model validation:
          (_      , Concrete (Just (_isSat, env))) -> do
                        let bad why conc = error $ unlines [ ""
                                                           , "*** Data.SBV: " ++ why
                                                           , "***"
                                                           , "***   To turn validation off, use `cfg{validateModel = False}`"
                                                           , "***"
                                                           , "*** " ++ conc
                                                           ]

                            cant   = "Validation engine is not capable of handling this case. Failed to validate."
                            report = "Please report this as a bug in SBV!"

                        case () of
                          () | isUserSort k -> bad ("Cannot validate models in the presence of user defined kinds, saw: "             ++ show k) cant

                          _  -> do (NamedSymVar sv internalName) <- newSV st k

                                   let nm = fromMaybe (T.unpack internalName) mbNm
                                       nsv = toNamedSV' sv nm

                                       -- Ignore the context equivalence check here. When validating, we are in a different
                                       -- context; so they won't match
                                       same (NamedSymVar (SV _ (NodeId (_, ll1, li1))) _)
                                            (NamedSymVar (SV _ (NodeId (_, ll2, li2))) _) = (ll1, li1) == (ll2, li2)

                                       cv = case [v | (nsv', v) <- env, nsv `same` nsv'] of
                                              []    -> if isTracker
                                                       then  -- The sole purpose of a tracker variable is to send the optimization
                                                             -- directive to the solver, so we can name "expressions" that are minimized
                                                             -- or maximized. There will be no constraints on these when we are doing
                                                             -- the validation; in fact they will not even be used anywhere during a
                                                             -- validation run. So, simply push a zero value that inhabits all metrics.
                                                             mkConstCV k (0::Integer)
                                                       else bad ("Cannot locate variable: " ++ show (nsv, k)) report
                                              [c]  -> c
                                              r    -> bad (   "Found multiple matching values for variable: " ++ show nsv
                                                           ++ "\n*** " ++ show r) report

                                   mkC cv

-- | Introduce a new user name. We simply append a suffix if we have seen this variable before.
introduceUserName :: State -> (Bool, Bool) -> String -> Kind -> Quantifier -> SV -> IO SVal
introduceUserName st@State{runMode} (isQueryVar, isTracker) nmOrig k q sv = do
        old <- allInputs <$> readIORef (rinps st)

        let nm  = mkUnique (T.pack nmOrig) old

        -- If this is not a query variable and we're in a query, reject it.
        -- See https://github.com/LeventErkok/sbv/issues/554 for the rationale.
        -- In theory, it should be possible to support this, but fixing it is
        -- rather costly as we'd have to track the regular updates and sync the
        -- incremental state appropriately. Instead, we issue an error message
        -- and ask the user to obey the query mode rules.
        rm <- readIORef runMode
        case rm of
          SMTMode _ IRun _ _ | not isQueryVar -> noInteractiveEver [ "Adding a new input variable in query mode: " ++ show nm
                                                                   , ""
                                                                   , "Hint: Use freshVar/freshVar_ for introducing new inputs in query mode."
                                                                   ]
          _                                   -> pure ()

        if isTracker && q == ALL
           then error $ "SBV: Impossible happened! A universally quantified tracker variable is being introduced: " ++ show nm
           else do let newInp olds = case q of
                                      EX  -> toNamedSV sv nm : olds
                                      ALL -> noInteractive [ "Adding a new universally quantified variable: "
                                                           , "  Name      : " ++ show nm
                                                           , "  Kind      : " ++ show k
                                                           , "  Quantifier: Universal"
                                                           , "  Node      : " ++ show sv
                                                           , "Only existential variables are supported in query mode."
                                                           ]
                   if isTracker
                      then modifyState st rinps (addInternInput sv nm)
                                     $ noInteractive ["Adding a new tracker variable in interactive mode: " ++ show nm]
                      else modifyState st rinps (addUserInput sv nm)
                                     $ modifyIncState st rNewInps newInp
                   return $ SVal k $ Right $ cache (const (return sv))

   where -- The following can be rather slow if we keep reusing the same prefix, but I doubt it'll be a problem in practice
         -- Also, the following will fail if we span the range of integers without finding a match, but your computer would
         -- die way ahead of that happening if that's the case!
         mkUnique :: T.Text -> Set.Set Name -> T.Text
         mkUnique prefix names = case dropWhile (`Set.member` names) (prefix : [prefix <> "_" <> T.pack (show i) | i <- [(0::Int)..]]) of
                                   h:_ -> h
                                   _   -> error $ "mkUnique: Impossible happened! Couldn't get a unique name for " ++ show (prefix, names)

-- | Create a new state
mkNewState :: MonadIO m => SMTConfig -> SBVRunMode -> m State
mkNewState cfg currentRunMode = liftIO $ do
     currTime           <- getCurrentTime
     progInfo           <- newIORef ProgInfo { hasQuants         = False
                                             , progSpecialRels   = []
                                             , progTransClosures = []
                                             }
     rm                 <- newIORef currentRunMode
     ctr                <- newIORef (-2) -- start from -2; False and True will always occupy the first two elements
     lambda             <- newIORef $ case currentRunMode of
                                        SMTMode{}   -> 0
                                        CodeGen{}   -> 0
                                        Concrete{}  -> 0
                                        LambdaGen i -> i
     cInfo              <- newIORef []
     observes           <- newIORef mempty
     pgm                <- newIORef (SBVPgm S.empty)
     emap               <- newIORef Map.empty
     cmap               <- newIORef Map.empty
     inps               <- newIORef mempty
     lambdaInps         <- newIORef mempty
     outs               <- newIORef []
     tables             <- newIORef Map.empty
     arrays             <- newIORef IMap.empty
     userFuncs          <- newIORef Set.empty
     uis                <- newIORef Map.empty
     cgs                <- newIORef Map.empty
     defns              <- newIORef []
     swCache            <- newIORef IMap.empty
     aiCache            <- newIORef IMap.empty
     usedKinds          <- newIORef Set.empty
     usedLbls           <- newIORef Set.empty
     cstrs              <- newIORef S.empty
     pvs                <- newIORef []
     smtOpts            <- newIORef []
     optGoals           <- newIORef []
     asserts            <- newIORef []
     outstandingAsserts <- newIORef False
     istate             <- newIORef =<< newIncState
     qstate             <- newIORef Nothing
     ctx                <- genSBVContext
     pure $ State { sbvContext          = ctx
                  , runMode             = rm
                  , stCfg               = cfg
                  , startTime           = currTime
                  , rProgInfo           = progInfo
                  , pathCond            = SVal KBool (Left trueCV)
                  , rIncState           = istate
                  , rCInfo              = cInfo
                  , rObservables        = observes
                  , rctr                = ctr
                  , rLambdaLevel        = lambda
                  , rUsedKinds          = usedKinds
                  , rUsedLbls           = usedLbls
                  , rinps               = inps
                  , rlambdaInps         = lambdaInps
                  , routs               = outs
                  , rtblMap             = tables
                  , spgm                = pgm
                  , rconstMap           = cmap
                  , rArrayMap           = arrays
                  , rexprMap            = emap
                  , rUserFuncs          = userFuncs
                  , rUIMap              = uis
                  , rCgMap              = cgs
                  , rDefns              = defns
                  , rSVCache            = swCache
                  , rAICache            = aiCache
                  , rConstraints        = cstrs
                  , rPartitionVars      = pvs
                  , rSMTOptions         = smtOpts
                  , rOptGoals           = optGoals
                  , rAsserts            = asserts
                  , rOutstandingAsserts = outstandingAsserts
                  , rQueryState         = qstate
                  , parentState         = Nothing
                  }

-- | Generalization of 'Data.SBV.runSymbolic'
runSymbolic :: MonadIO m => SMTConfig -> SBVRunMode -> SymbolicT m a -> m (a, Result)
runSymbolic cfg currentRunMode comp = do
   st <- mkNewState cfg currentRunMode
   runSymbolicInState st comp

-- | Catch the catastrophic case of context mismatch
contextMismatchError :: SBVContext -> SBVContext -> Maybe (Int, Int) -> Maybe (Int, Int) -> a
contextMismatchError ctx1 ctx2 level1 level2 = error $ unlines $ prefix ++ rest
  where prefix | ctx1 /= ctx2 = [ "Data.SBV: Mismatched contexts detected."
                                , "***"
                                , "*** Current context: " ++ show ctx1
                                , "*** Mixed with     : " ++ show ctx2
                                ]
               | True         = [ "Data.SBV: Mismatched levels detected in the same context."
                                , "***"
                                , "*** Refers to: " ++ show level1
                                , "*** And also : " ++ show level2
                                ]
        rest = [ "***"
               , "*** This happens if you call a proof-function (prove/sat/runSMT/isSatisfiable) etc."
               , "*** while another one is in execution, or use results from one such call in another."
               , "*** Please avoid such nested calls, all interactions should be from the same context."
               , "*** See https://github.com/LeventErkok/sbv/issues/71 for several examples."
               ]

-- | Run a symbolic computation in a given state
runSymbolicInState :: MonadIO m => State -> SymbolicT m a -> m (a, Result)
runSymbolicInState st (SymbolicT c) = do
   _ <- liftIO $ newConst st falseCV -- s(-2) == falseSV
   _ <- liftIO $ newConst st trueCV  -- s(-1) == trueSV
   r <- runReaderT c st
   res <- liftIO $ extractSymbolicSimulationState st

   -- Check that the state wasn't clobbered in any way
   let check ctx | ctx == sbvContext st || ctx == globalSBVContext
                 = pure ()
                 | True
                 = contextMismatchError (sbvContext st) ctx Nothing Nothing

   mapM_ check $ nub $ G.universeBi res

   -- Clean-up after ourselves
   qs <- liftIO $ readIORef $ rQueryState st
   case qs of
     Nothing                         -> return ()
     Just QueryState{queryTerminate} -> liftIO queryTerminate

   return (r, res)

-- | Grab the program from a running symbolic simulation state.
extractSymbolicSimulationState :: State -> IO Result
extractSymbolicSimulationState st@State{ runMode=rrm
                                       , spgm=pgm, rinps=inps, rlambdaInps=linps, routs=outs, rtblMap=tables, rArrayMap=arrays
                                       , rUIMap=uis, rDefns=defns
                                       , rAsserts=asserts, rUsedKinds=usedKinds, rCgMap=cgs, rCInfo=cInfo, rConstraints=cstrs
                                       , rObservables=observes, rProgInfo=progInfo
                                       } = do
   SBVPgm rpgm  <- readIORef pgm

   rm <- readIORef rrm

   inpsO <- do Inputs{userInputs, internInputs} <- readIORef inps
               ls <- readIORef linps

               let lambdaOnly = case rm of
                                  SMTMode{}   -> False
                                  CodeGen{}   -> False
                                  Concrete{}  -> False
                                  LambdaGen{} -> True
                   topInps = (F.toList userInputs, F.toList internInputs)
                   lamInps = F.toList ls

               if lambdaOnly
                  then case topInps of
                          ([], []) -> pure $ ResultLamInps (F.toList ls)
                          (xs, ys) -> error $ unlines [ ""
                                                      , "*** Data.SBV: Impossible happened; saw inputs in lambda mode."
                                                      , "***"
                                                      , "***   Inps    : " ++ show xs
                                                      , "***   Trackers: " ++ show ys
                                                      ]
                  else case lamInps of
                          [] -> pure $ ResultTopInps topInps
                          _  -> error $ unlines [ ""
                                                , "*** Data.SBV: Impossible happened; saw lambda inputs in regular mode."
                                                , "***"
                                                , "***   Params: " ++ show lamInps
                                                ]

   outsO <- reverse <$> readIORef outs

   let swap  (a, b)              = (b, a)
       cmp   (a, _) (b, _)       = a `compare` b
       arrange (i, (at, rt, es)) = ((i, at, rt), es)

   constMap <- readIORef (rconstMap st)
   let cnsts = sortBy cmp . map swap . Map.toList $ constMap

   tbls  <- map arrange . sortBy cmp . map swap . Map.toList <$> readIORef tables
   arrs  <- IMap.toAscList <$> readIORef arrays
   ds    <- reverse <$> readIORef defns
   unint <- do unints <- Map.toList <$> readIORef uis
               -- drop those that has a definition associated with it
               let defineds = mapMaybe (smtDefGivenName . fst) ds
               pure [ui | ui@(nm, _) <- unints, nm `notElem` defineds]
   knds  <- readIORef usedKinds
   cgMap <- Map.toList <$> readIORef cgs

   traceVals   <- reverse <$> readIORef cInfo
   observables <- reverse . fmap (\(n,f,sv) -> (T.unpack n, f, sv)) . F.toList
                  <$> readIORef observes
   extraCstrs  <- readIORef cstrs
   assertions  <- reverse <$> readIORef asserts

   pinfo <- readIORef progInfo

   return $ Result pinfo knds traceVals observables cgMap inpsO (constMap, cnsts) tbls arrs unint ds (SBVPgm rpgm) extraCstrs assertions outsO

-- | Generalization of 'Data.SBV.addNewSMTOption'
addNewSMTOption :: MonadSymbolic m => SMTOption -> m ()
addNewSMTOption o = do st <- symbolicEnv
                       liftIO $ modifyState st rSMTOptions (o:) (return ())

-- | Generalization of 'Data.SBV.imposeConstraint'
imposeConstraint :: MonadSymbolic m => Bool -> [(String, String)] -> SVal -> m ()
imposeConstraint isSoft attrs c = do st <- symbolicEnv
                                     rm <- liftIO $ readIORef (runMode st)

                                     case rm of
                                       CodeGen -> error "SBV: constraints are not allowed in code-generation"
                                       _       -> liftIO $ do mapM_ (registerLabel "Constraint" st) [nm | (":named",  nm) <- attrs]
                                                              internalConstraint st isSoft attrs c

-- | Require a boolean condition to be true in the state. Only used for internal purposes.
internalConstraint :: State -> Bool -> [(String, String)] -> SVal -> IO ()
internalConstraint st isSoft attrs b = do v <- svToSV st b

                                          rm <- liftIO $ readIORef (runMode st)

                                          -- Are we running validation? If so, we always want to
                                          -- add the constraint for debug purposes. Otherwise
                                          -- we only add it if it's interesting; i.e., not directly
                                          -- true or has some attributes.
                                          let isValidating = case rm of
                                                               SMTMode _ _ _ cfg -> validationRequested cfg
                                                               CodeGen           -> False
                                                               LambdaGen{}       -> False
                                                               Concrete Nothing  -> False
                                                               Concrete (Just _) -> True   -- The case when we *are* running the validation

                                          let c           = (isSoft, attrs, v)
                                              interesting = v /= trueSV || not (null attrs)

                                          when (isValidating || interesting) $
                                               modifyState st rConstraints (S.|> c)
                                                            $ modifyIncState st rNewConstraints (S.|> c)

-- | Generalization of 'Data.SBV.addSValOptGoal'
addSValOptGoal :: MonadSymbolic m => Objective SVal -> m ()
addSValOptGoal obj = do st <- symbolicEnv

                        -- create the tracking variable here for the metric
                        let mkGoal nm orig = liftIO $ do origSV  <- svToSV st orig
                                                         track   <- svMkTrackerVar (kindOf orig) nm st
                                                         trackSV <- svToSV st track
                                                         return (origSV, trackSV)

                        let walk (Minimize          nm v)     = Minimize nm                     <$> mkGoal nm v
                            walk (Maximize          nm v)     = Maximize nm                     <$> mkGoal nm v
                            walk (AssertWithPenalty nm v mbP) = flip (AssertWithPenalty nm) mbP <$> mkGoal nm v

                        !obj' <- walk obj
                        liftIO $ modifyState st rOptGoals (obj' :)
                                           $ noInteractive [ "Adding an optimization objective:"
                                                           , "  Objective: " ++ show obj
                                                           ]

-- | Generalization of 'Data.SBV.outputSVal'
outputSVal :: MonadSymbolic m => SVal -> m ()
outputSVal (SVal _ (Left c)) = do
  st <- symbolicEnv
  sv <- liftIO $ newConst st c
  liftIO $ modifyState st routs (sv:) (return ())
outputSVal (SVal _ (Right f)) = do
  st <- symbolicEnv
  sv <- liftIO $ uncache f st
  liftIO $ modifyState st routs (sv:) (return ())

---------------------------------------------------------------------------------
-- * Cached values
---------------------------------------------------------------------------------

-- | We implement a peculiar caching mechanism, applicable to the use case in
-- implementation of SBV's.  Whenever we do a state based computation, we do
-- not want to keep on evaluating it in the then-current state. That will
-- produce essentially a semantically equivalent value. Thus, we want to run
-- it only once, and reuse that result, capturing the sharing at the Haskell
-- level. This is similar to the "type-safe observable sharing" work, but also
-- takes into the account of how symbolic simulation executes.
--
-- See Andy Gill's type-safe observable sharing trick for the inspiration behind
-- this technique: <http://ku-fpg.github.io/files/Gill-09-TypeSafeReification.pdf>
--
-- Note that this is *not* a general memo utility!
newtype Cached a = Cached (State -> IO a)

-- | Cache a state-based computation
cache :: (State -> IO a) -> Cached a
cache = Cached

-- | Uncache a previously cached computation
uncache :: Cached SV -> State -> IO SV
uncache = uncacheGen rSVCache

-- | An SMT array index is simply an int value, and the context this array was created in
data ArrayIndex = ArrayIndex { unArrayIndex   :: Int
                             , unArrayContext :: SBVContext
                             }
               deriving (Eq, Ord, G.Data)

-- | We simply show indexes as the underlying integer
instance Show ArrayIndex where
  show = show . unArrayIndex

-- | Uncache, retrieving SMT array indexes
uncacheAI :: Cached ArrayIndex -> State -> IO ArrayIndex
uncacheAI = uncacheGen rAICache

-- | Generic uncaching. Note that this is entirely safe, since we do it in the IO monad.
uncacheGen :: (State -> IORef (Cache a)) -> Cached a -> State -> IO a
uncacheGen getCache (Cached f) st = do
        let rCache = getCache st
        stored <- readIORef rCache
        sn <- f `seq` makeStableName f
        let h = hashStableName sn
        case (h `IMap.lookup` stored) >>= (sn `lookup`) of
          Just r  -> return r
          Nothing -> do r <- f st
                        r `seq` R.modifyIORef' rCache (IMap.insertWith (++) h [(sn, r)])
                        return r

-- | Representation of SMTLib Program versions. As of June 2015, we're dropping support
-- for SMTLib1, and supporting SMTLib2 only. We keep this data-type around in case
-- SMTLib3 comes along and we want to support 2 and 3 simultaneously.
data SMTLibVersion = SMTLib2
                   deriving (Bounded, Enum, Eq, Show)

-- | The extension associated with the version
smtLibVersionExtension :: SMTLibVersion -> String
smtLibVersionExtension SMTLib2 = "smt2"

-- | Representation of an SMT-Lib program. The second [String] are the function definitions,
-- which is *replicated* in the first one. There are cases where that we need the second part on its own.
data SMTLibPgm = SMTLibPgm SMTLibVersion [String] [String]

instance NFData SMTLibVersion where rnf a                 = a `seq` ()
instance NFData SMTLibPgm     where rnf (SMTLibPgm v p d) = rnf v `seq` rnf p `seq` rnf d

instance Show SMTLibPgm where
  show (SMTLibPgm _ pgm _) = intercalate "\n" pgm

-- Other Technicalities..
instance NFData CV where
  rnf (CV x y) = x `seq` y `seq` ()

instance NFData GeneralizedCV where
  rnf (ExtendedCV e) = e `seq` ()
  rnf (RegularCV  c) = c `seq` ()

#if MIN_VERSION_base(4,9,0)
#else
-- Can't really force this, but not a big deal
instance NFData CallStack where
  rnf _ = ()
#endif

instance NFData NamedSymVar where
  rnf (NamedSymVar s n) = rnf s `seq` rnf n

instance NFData Result where
  rnf (Result hasQuants kindInfo qcInfo obs cgs inps consts tbls arrs uis axs pgm cstr asserts outs)
        = rnf hasQuants `seq` rnf kindInfo `seq` rnf qcInfo `seq` rnf obs    `seq` rnf cgs
                        `seq` rnf inps     `seq` rnf consts `seq` rnf tbls
                        `seq` rnf arrs     `seq` rnf uis    `seq` rnf axs
                        `seq` rnf pgm      `seq` rnf cstr   `seq` rnf asserts
                        `seq` rnf outs
instance NFData Kind         where rnf a          = seq a ()
instance NFData ArrayContext where rnf a          = seq a ()
instance NFData SV           where rnf a          = seq a ()
instance NFData SBVExpr      where rnf a          = seq a ()
instance NFData Quantifier   where rnf a          = seq a ()
instance NFData SBVType      where rnf a          = seq a ()
instance NFData SBVPgm       where rnf a          = seq a ()
instance NFData (Cached a)   where rnf (Cached f) = f `seq` ()
instance NFData SVal         where rnf (SVal x y) = rnf x `seq` rnf y

instance NFData SMTResult where
  rnf (Unsatisfiable _   m   ) = rnf m
  rnf (Satisfiable   _   m   ) = rnf m
  rnf (DeltaSat      _ p m   ) = rnf m `seq` rnf p
  rnf (SatExtField   _   m   ) = rnf m
  rnf (Unknown       _   m   ) = rnf m
  rnf (ProofError    _   m mr) = rnf m `seq` rnf mr

instance NFData SMTModel where
  rnf (SMTModel objs bndgs assocs uifuns) = rnf objs `seq` rnf bndgs `seq` rnf assocs `seq` rnf uifuns

instance NFData SMTScript where
  rnf (SMTScript b m) = rnf b `seq` rnf m

-- | Translation tricks needed for specific capabilities afforded by each solver
data SolverCapabilities = SolverCapabilities {
         supportsQuantifiers        :: Bool           -- ^ Supports SMT-Lib2 style quantifiers?
       , supportsDefineFun          :: Bool           -- ^ Supports define-fun construct?
       , supportsDistinct           :: Bool           -- ^ Supports calls to distinct?
       , supportsBitVectors         :: Bool           -- ^ Supports bit-vectors?
       , supportsUninterpretedSorts :: Bool           -- ^ Supports SMT-Lib2 style uninterpreted-sorts
       , supportsUnboundedInts      :: Bool           -- ^ Supports unbounded integers?
       , supportsInt2bv             :: Bool           -- ^ Supports int2bv?
       , supportsReals              :: Bool           -- ^ Supports reals?
       , supportsApproxReals        :: Bool           -- ^ Supports printing of approximations of reals?
       , supportsDeltaSat           :: Maybe String   -- ^ Supports delta-satisfiability? (With given precision query)
       , supportsIEEE754            :: Bool           -- ^ Supports floating point numbers?
       , supportsSets               :: Bool           -- ^ Supports set operations?
       , supportsOptimization       :: Bool           -- ^ Supports optimization routines?
       , supportsPseudoBooleans     :: Bool           -- ^ Supports pseudo-boolean operations?
       , supportsCustomQueries      :: Bool           -- ^ Supports interactive queries per SMT-Lib?
       , supportsGlobalDecls        :: Bool           -- ^ Supports global declarations? (Needed for push-pop.)
       , supportsDataTypes          :: Bool           -- ^ Supports datatypes?
       , supportsFoldAndMap         :: Bool           -- ^ Does it support fold and map?
       , supportsSpecialRels        :: Bool           -- ^ Does it support special relations (orders, transitive closure etc.)
       , supportsDirectAccessors    :: Bool           -- ^ Supports data-type accessors without full ascription?
       , supportsFlattenedModels    :: Maybe [String] -- ^ Supports flattened model output? (With given config lines.)
       }

-- | Solver configuration. See also 'Data.SBV.z3', 'Data.SBV.yices', 'Data.SBV.cvc4', 'Data.SBV.boolector', 'Data.SBV.mathSAT', etc.
-- which are instantiations of this type for those solvers, with reasonable defaults. In particular, custom configuration can be
-- created by varying those values. (Such as @z3{verbose=True}@.)
--
-- Most fields are self explanatory. The notion of precision for printing algebraic reals stems from the fact that such values does
-- not necessarily have finite decimal representations, and hence we have to stop printing at some depth. It is important to
-- emphasize that such values always have infinite precision internally. The issue is merely with how we print such an infinite
-- precision value on the screen. The field 'printRealPrec' controls the printing precision, by specifying the number of digits after
-- the decimal point. The default value is 16, but it can be set to any positive integer.
--
-- When printing, SBV will add the suffix @...@ at the end of a real-value, if the given bound is not sufficient to represent the real-value
-- exactly. Otherwise, the number will be written out in standard decimal notation. Note that SBV will always print the whole value if it
-- is precise (i.e., if it fits in a finite number of digits), regardless of the precision limit. The limit only applies if the representation
-- of the real value is not finite, i.e., if it is not rational.
--
-- The 'printBase' field can be used to print numbers in base 2, 10, or 16.
--
-- The 'crackNum' field can be used to display numbers in detail, all its bits and how they are laid out in memory. Works with all bounded number types
-- (i.e., SWord and SInt), but also with floats. It is particularly useful with floating-point numbers, as it shows you how they are laid out in
-- memory following the IEEE754 rules.
data SMTConfig = SMTConfig {
         verbose                     :: Bool                -- ^ Debug mode
       , timing                      :: Timing              -- ^ Print timing information on how long different phases took (construction, solving, etc.)
       , printBase                   :: Int                 -- ^ Print integral literals in this base (2, 10, and 16 are supported.)
       , printRealPrec               :: Int                 -- ^ Print algebraic real values with this precision. (SReal, default: 16)
       , crackNum                    :: Bool                -- ^ For each numeric value, show it in detail in the model with its bits spliced out. Good for floats.
       , crackNumSurfaceVals         :: [(String, Integer)] -- ^ For crackNum: The surface representation of variables, if available
       , satCmd                      :: String              -- ^ Usually "(check-sat)". However, users might tweak it based on solver characteristics.
       , allSatMaxModelCount         :: Maybe Int           -- ^ In a 'Data.SBV.allSat' call, return at most this many models. If nothing, return all.
       , allSatPrintAlong            :: Bool                -- ^ In a 'Data.SBV.allSat' call, print models as they are found.
       , allSatTrackUFs              :: Bool                -- ^ In a 'Data.SBV.allSat' call, should we try to extract values of uninterpreted functions?
       , isNonModelVar               :: String -> Bool      -- ^ When constructing a model, ignore variables whose name satisfy this predicate. (Default: (const False), i.e., don't ignore anything)
       , validateModel               :: Bool                -- ^ If set, SBV will attempt to validate the model it gets back from the solver.
       , optimizeValidateConstraints :: Bool                -- ^ Validate optimization results. NB: Does NOT make sure the model is optimal, just checks they satisfy the constraints.
       , transcript                  :: Maybe FilePath      -- ^ If Just, the entire interaction will be recorded as a playable file (for debugging purposes mostly)
       , smtLibVersion               :: SMTLibVersion       -- ^ What version of SMT-lib we use for the tool
       , dsatPrecision               :: Maybe Double        -- ^ Delta-sat precision
       , solver                      :: SMTSolver           -- ^ The actual SMT solver.
       , extraArgs                   :: [String]            -- ^ Extra command line arguments to pass to the solver.
       , roundingMode                :: RoundingMode        -- ^ Rounding mode to use for floating-point conversions
       , solverSetOptions            :: [SMTOption]         -- ^ Options to set as we start the solver
       , ignoreExitCode              :: Bool                -- ^ If true, we shall ignore the exit code upon exit. Otherwise we require ExitSuccess.
       , redirectVerbose             :: Maybe FilePath      -- ^ Redirect the verbose output to this file if given. If Nothing, stdout is implied.
       }

-- | Ignore internal names and those the user told us to
mustIgnoreVar :: SMTConfig -> String -> Bool
mustIgnoreVar cfg s = "__internal_sbv" `isPrefixOf` s || isNonModelVar cfg s

-- | We show the name of the solver for the config. Arguably this is misleading, but better than nothing.
instance Show SMTConfig where
  show = show . name . solver

-- | Returns true if we have to perform validation
validationRequested :: SMTConfig -> Bool
validationRequested SMTConfig{validateModel, optimizeValidateConstraints} = validateModel || optimizeValidateConstraints

-- We're just seq'ing top-level here, it shouldn't really matter. (i.e., no need to go deeper.)
instance NFData SMTConfig where
  rnf SMTConfig{} = ()

-- | A model, as returned by a solver
data SMTModel = SMTModel {
       modelObjectives :: [(String, GeneralizedCV)]                                     -- ^ Mapping of symbolic values to objective values.
     , modelBindings   :: Maybe [(NamedSymVar, CV)]                                     -- ^ Mapping of input variables as reported by the solver. Only collected if model validation is requested.
     , modelAssocs     :: [(String, CV)]                                                -- ^ Mapping of symbolic values to constants.
     , modelUIFuns     :: [(String, (Bool, SBVType, Either String ([([CV], CV)], CV)))] -- ^ Mapping of uninterpreted functions to association lists in the model.
                                                                                        -- Note that an uninterpreted constant (function of arity 0) will be stored
                                                                                        -- in the 'modelAssocs' field. Left is used when the function returned is too
                                                                                        -- difficult for SBV to figure out what it means
     }
     deriving Show

-- | The result of an SMT solver call. Each constructor is tagged with
-- the 'SMTConfig' that created it so that further tools can inspect it
-- and build layers of results, if needed. For ordinary uses of the library,
-- this type should not be needed, instead use the accessor functions on
-- it. (Custom Show instances and model extractors.)
data SMTResult = Unsatisfiable SMTConfig (Maybe [String])            -- ^ Unsatisfiable. If unsat-cores are enabled, they will be returned in the second parameter.
               | Satisfiable   SMTConfig SMTModel                    -- ^ Satisfiable with model
               | DeltaSat      SMTConfig (Maybe String) SMTModel     -- ^ Delta satisfiable with queried string if available and model
               | SatExtField   SMTConfig SMTModel                    -- ^ Prover returned a model, but in an extension field containing Infinite/epsilon
               | Unknown       SMTConfig SMTReasonUnknown            -- ^ Prover returned unknown, with the given reason
               | ProofError    SMTConfig [String] (Maybe SMTResult)  -- ^ Prover errored out, with possibly a bogus result

-- | A script, to be passed to the solver.
data SMTScript = SMTScript {
          scriptBody  :: String   -- ^ Initial feed
        , scriptModel :: [String] -- ^ Continuation script, to extract results
        }

-- | An SMT engine
type SMTEngine =  forall res.
                  SMTConfig         -- ^ current configuration
               -> State             -- ^ the state in which to run the engine
               -> String            -- ^ program
               -> (State -> IO res) -- ^ continuation
               -> IO res

-- | Solvers that SBV is aware of
data Solver = ABC
            | Boolector
            | Bitwuzla
            | CVC4
            | CVC5
            | DReal
            | MathSAT
            | Yices
            | Z3
            | OpenSMT
            deriving (Show, Enum, Bounded)

-- | An SMT solver
data SMTSolver = SMTSolver {
         name           :: Solver                -- ^ The solver in use
       , executable     :: String                -- ^ The path to its executable
       , preprocess     :: String -> String      -- ^ Each line sent to the solver will be passed through this function (typically id)
       , options        :: SMTConfig -> [String] -- ^ Options to provide to the solver
       , engine         :: SMTEngine             -- ^ The solver engine, responsible for interpreting solver output
       , capabilities   :: SolverCapabilities    -- ^ Various capabilities of the solver
       }

-- | Query execution context
data QueryContext = QueryInternal       -- ^ Triggered from inside SBV
                  | QueryExternal       -- ^ Triggered from user code

-- | Show instance for 'QueryContext', for debugging purposes
instance Show QueryContext where
   show QueryInternal = "Internal Query"
   show QueryExternal = "User Query"

{- HLint ignore type FPOp "Use camelCase" -}
{- HLint ignore type PBOp "Use camelCase" -}
{- HLint ignore type OvOp "Use camelCase" -}
{- HLint ignore type NROp "Use camelCase" -}
