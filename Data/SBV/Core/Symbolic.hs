-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.Symbolic
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Symbolic values
-----------------------------------------------------------------------------

{-# LANGUAGE    CPP                        #-}
{-# LANGUAGE    DeriveDataTypeable         #-}
{-# LANGUAGE    DeriveFunctor              #-}
{-# LANGUAGE    FlexibleInstances          #-}
{-# LANGUAGE    GeneralizedNewtypeDeriving #-}
{-# LANGUAGE    MultiParamTypeClasses      #-}
{-# LANGUAGE    NamedFieldPuns             #-}
{-# LANGUAGE    PatternGuards              #-}
{-# LANGUAGE    Rank2Types                 #-}
{-# LANGUAGE    ScopedTypeVariables        #-}
{-# LANGUAGE    TupleSections              #-}
{-# LANGUAGE    TypeOperators              #-}
{-# LANGUAGE    TypeSynonymInstances       #-}
{-# OPTIONS_GHC -fno-warn-orphans          #-}

module Data.SBV.Core.Symbolic
  ( NodeId(..)
  , SW(..), swKind, trueSW, falseSW
  , Op(..), PBOp(..), OvOp(..), FPOp(..), StrOp(..), RegExp(..)
  , Quantifier(..), needsExistentials
  , RoundingMode(..)
  , SBVType(..), svUninterpreted, newUninterpreted, addAxiom
  , SVal(..)
  , svMkSymVar, sWordN, sWordN_, sIntN, sIntN_
  , ArrayContext(..), ArrayInfo
  , svToSW, svToSymSW, forceSWArg
  , SBVExpr(..), newExpr, isCodeGenMode, isSafetyCheckingIStage, isRunIStage, isSetupIStage
  , Cached, cache, uncache, modifyState, modifyIncState
  , ArrayIndex(..), FArrayIndex(..), uncacheAI, uncacheFAI
  , NamedSymVar
  , getSValPathCondition, extendSValPathCondition
  , getTableIndex
  , SBVPgm(..), Symbolic, runSymbolic, State(..), withNewIncState, IncState(..), incrementInternalCounter
  , inSMTMode, SBVRunMode(..), IStage(..), Result(..)
  , registerKind, registerLabel, recordObservable
  , addAssertion, addNewSMTOption, imposeConstraint, internalConstraint, internalVariable
  , SMTLibPgm(..), SMTLibVersion(..), smtLibVersionExtension
  , SolverCapabilities(..)
  , extractSymbolicSimulationState
  , OptimizeStyle(..), Objective(..), Penalty(..), objectiveName, addSValOptGoal
  , Query(..), QueryState(..), QueryContext(..)
  , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..), SMTEngine
  , outputSVal
  ) where

import Control.Arrow            (first, second, (***))
import Control.DeepSeq          (NFData(..))
import Control.Monad            (when, unless)
import Control.Monad.Reader     (MonadReader, ReaderT, ask, runReaderT)
import Control.Monad.State.Lazy (MonadState, StateT(..))
import Control.Monad.Trans      (MonadIO, liftIO)
import Data.Char                (isAlpha, isAlphaNum, toLower)
import Data.IORef               (IORef, newIORef, readIORef)
import Data.List                (intercalate, sortBy)
import Data.Maybe               (isJust, fromJust, fromMaybe, listToMaybe)
import Data.String              (IsString(fromString))

import Data.Time (getCurrentTime, UTCTime)

import GHC.Stack

import qualified Data.IORef         as R    (modifyIORef')
import qualified Data.Generics      as G    (Data(..))
import qualified Data.IntMap.Strict as IMap (IntMap, empty, toAscList, lookup, insertWith)
import qualified Data.Map.Strict    as Map  (Map, empty, toList, lookup, insert, size)
import qualified Data.Set           as Set  (Set, empty, toList, insert, member)
import qualified Data.Foldable      as F    (toList)
import qualified Data.Sequence      as S    (Seq, empty, (|>))

import System.Mem.StableName

import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.SMT.SMTLibNames
import Data.SBV.Utils.TDiff (Timing)
import Data.SBV.Utils.Lib   (stringToQFS)

import Data.SBV.Control.Types

-- | A symbolic node id
newtype NodeId = NodeId Int deriving (Eq, Ord)

-- | A symbolic word, tracking it's signedness and size.
data SW = SW !Kind !NodeId deriving (Eq, Ord)

instance HasKind SW where
  kindOf (SW k _) = k

instance Show SW where
  show (SW _ (NodeId n))
    | n < 0 = "s_" ++ show (abs n)
    | True  = 's' : show n

-- | Kind of a symbolic word.
swKind :: SW -> Kind
swKind (SW k _) = k

-- | Forcing an argument; this is a necessary evil to make sure all the arguments
-- to an uninterpreted function are evaluated before called; the semantics of uinterpreted
-- functions is necessarily strict; deviating from Haskell's
forceSWArg :: SW -> IO ()
forceSWArg (SW k n) = k `seq` n `seq` return ()

-- | Constant False as an SW. Note that this value always occupies slot -2.
falseSW :: SW
falseSW = SW KBool $ NodeId (-2)

-- | Constant True as an SW. Note that this value always occupies slot -1.
trueSW :: SW
trueSW  = SW KBool $ NodeId (-1)

-- | Symbolic operations
data Op = Plus
        | Times
        | Minus
        | UNeg
        | Abs
        | Quot
        | Rem
        | Equal
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
        | LkUp (Int, Kind, Kind, Int) !SW !SW   -- (table-index, arg-type, res-type, length of the table) index out-of-bounds-value
        | ArrEq   ArrayIndex ArrayIndex         -- Array equality
        | ArrRead ArrayIndex
        | KindCast Kind Kind
        | Uninterpreted String
        | Label String                          -- Essentially no-op; useful for code generation to emit comments.
        | IEEEFP FPOp                           -- Floating-point ops, categorized separately
        | PseudoBoolean PBOp                    -- Pseudo-boolean ops, categorized separately
        | OverflowOp    OvOp                    -- Overflow-ops, categorized separately
        | StrOp StrOp                           -- String ops, categorized separately
        deriving (Eq, Ord)

-- | Floating point operations
data FPOp = FP_Cast        Kind Kind SW   -- From-Kind, To-Kind, RoundingMode. This is "value" conversion
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
          deriving (Eq, Ord)

-- Note that the show instance maps to the SMTLib names. We need to make sure
-- this mapping stays correct through SMTLib changes. The only exception
-- is FP_Cast; where we handle different source/origins explicitly later on.
instance Show FPOp where
   show (FP_Cast f t r)      = "(FP_Cast: " ++ show f ++ " -> " ++ show t ++ ", using RM [" ++ show r ++ "])"
   show (FP_Reinterpret f t) = case (f, t) of
                                  (KBounded False 32, KFloat)  -> "(_ to_fp 8 24)"
                                  (KBounded False 64, KDouble) -> "(_ to_fp 11 53)"
                                  _                            -> error $ "SBV.FP_Reinterpret: Unexpected conversion: " ++ show f ++ " to " ++ show t
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

-- | Pseudo-boolean operations
data PBOp = PB_AtMost  Int        -- ^ At most k
          | PB_AtLeast Int        -- ^ At least k
          | PB_Exactly Int        -- ^ Exactly k
          | PB_Le      [Int] Int  -- ^ At most k,  with coefficients given. Generalizes PB_AtMost
          | PB_Ge      [Int] Int  -- ^ At least k, with coefficients given. Generalizes PB_AtLeast
          | PB_Eq      [Int] Int  -- ^ Exactly k,  with coefficients given. Generalized PB_Exactly
          deriving (Eq, Ord, Show)

-- | Overflow operations
data OvOp = Overflow_SMul_OVFL   -- ^ Signed multiplication overflow
          | Overflow_SMul_UDFL   -- ^ Signed multiplication underflow
          | Overflow_UMul_OVFL   -- ^ Unsigned multiplication overflow
          deriving (Eq, Ord)

-- | Show instance. It's important that these follow the internal z3 names
instance Show OvOp where
  show Overflow_SMul_OVFL = "bvsmul_noovfl"
  show Overflow_SMul_UDFL = "bvsmul_noudfl"
  show Overflow_UMul_OVFL = "bvumul_noovfl"

-- | String operations. Note that we do not define `StrAt` as it translates to `StrSubStr` trivially.
data StrOp = StrConcat       -- ^ Concatenation of one or more strings
           | StrLen          -- ^ String length
           | StrUnit         -- ^ Unit string
           | StrSubstr       -- ^ Retrieves substring of @s@ at @offset@
           | StrIndexOf      -- ^ Retrieves first position of @sub@ in @s@, @-1@ if there are no occurrences
           | StrContains     -- ^ Does @s@ contain the substring @sub@?
           | StrPrefixOf     -- ^ Is @pre@ a prefix of @s@?
           | StrSuffixOf     -- ^ Is @suf@ a suffix of @s@?
           | StrReplace      -- ^ Replace the first occurrence of @src@ by @dst@ in @s@
           | StrStrToNat     -- ^ Retrieve integer encoded by string @s@ (ground rewriting only)
           | StrNatToStr     -- ^ Retrieve string encoded by integer @i@ (ground rewriting only)
           | StrInRe RegExp  -- ^ Check if string is in the regular expression
           deriving (Eq, Ord)

-- | Regular expressions. Note that regular expressions themselves are
-- concrete, but the `match` function from the 'RegExpMatchable' class
-- can check membership against a symbolic string/character. Also, we
-- are preferring a datatype approach here, as opposed to coming up with
-- some string-representation; there are way too many alternatives
-- already so inventing one isn't a priority. Please get in touch if you
-- would like a parser for this type as it might be easier to use.
data RegExp = Literal String       -- ^ Precisely match the given string
            | All                  -- ^ Accept every string
            | None                 -- ^ Accept no strings
            | Range Char Char      -- ^ Accept range of characters
            | Conc  [RegExp]       -- ^ Concatenation
            | KStar RegExp         -- ^ Kleene Star: Zero or more
            | KPlus RegExp         -- ^ Kleene Plus: One or more
            | Opt   RegExp         -- ^ Zero or one
            | Loop  Int Int RegExp -- ^ From @n@ repetitions to @m@ repetitions
            | Union [RegExp]       -- ^ Union of regular expressions
            | Inter RegExp RegExp  -- ^ Intersection of regular expressions
            deriving (Eq, Ord)

-- | With overloaded strings, we can have direct literal regular expressions.
instance IsString RegExp where
  fromString = Literal

-- | Regular expressions as a 'Num' instance. Note that
-- only `+` (union) and `*` (concatenation) make sense.
instance Num RegExp where
  -- flatten the concats to make them simpler
  Conc xs * y = Conc (xs ++ [y])
  x * Conc ys = Conc (x  :  ys)
  x * y       = Conc [x, y]

  -- flatten the unions to make them simpler
  Union xs + y = Union (xs ++ [y])
  x + Union ys = Union (x  : ys)
  x + y        = Union [x, y]

  abs         = error "Num.RegExp: no abs method"
  signum      = error "Num.RegExp: no signum method"

  fromInteger x
    | x == 0    = None
    | x == 1    = Literal ""   -- Unit for concatenation is the empty string
    | True      = error $ "Num.RegExp: Only 0 and 1 makes sense as a reg-exp, no meaning for: " ++ show x

  negate      = error "Num.RegExp: no negate method"

-- | Show instance for `RegExp`. The mapping is done so the outcome matches the
-- SMTLib string reg-exp operations
instance Show RegExp where
  show (Literal s)       = "(str.to.re \"" ++ stringToQFS s ++ "\")"
  show All               = "re.allchar"
  show None              = "re.nostr"
  show (Range ch1 ch2)   = "(re.range \"" ++ stringToQFS [ch1] ++ "\" \"" ++ stringToQFS [ch2] ++ "\")"
  show (Conc [])         = show (1 :: Integer)
  show (Conc [x])        = show x
  show (Conc xs)         = "(re.++ " ++ unwords (map show xs) ++ ")"
  show (KStar r)         = "(re.* " ++ show r ++ ")"
  show (KPlus r)         = "(re.+ " ++ show r ++ ")"
  show (Opt   r)         = "(re.opt " ++ show r ++ ")"
  show (Loop  lo hi r)
     | lo >= 0, hi >= lo = "((_ re.loop " ++ show lo ++ " " ++ show hi ++ ") " ++ show r ++ ")"
     | True              = error $ "Invalid regular-expression Loop with arguments: " ++ show (lo, hi)
  show (Inter r1 r2)     = "(re.inter " ++ show r1 ++ " " ++ show r2 ++ ")"
  show (Union [])        = "re.nostr"
  show (Union [x])       = show x
  show (Union xs)        = "(re.union " ++ unwords (map show xs) ++ ")"

-- | Show instance for `StrOp`. Note that the mapping here is
-- important to match the SMTLib equivalents, see here: <http://rise4fun.com/z3/tutorialcontent/sequences>
instance Show StrOp where
  show StrConcat   = "str.++"
  show StrLen      = "str.len"
  show StrUnit     = "seq.unit"      -- NB. The "seq" prefix is intentional; works uniformly.
  show StrSubstr   = "str.substr"
  show StrIndexOf  = "str.indexof"
  show StrContains = "str.contains"
  show StrPrefixOf = "str.prefixof"
  show StrSuffixOf = "str.suffixof"
  show StrReplace  = "str.replace"
  show StrStrToNat = "str.to.int"    -- NB. SMTLib uses "int" here though only nats are supported
  show StrNatToStr = "int.to.str"    -- NB. SMTLib uses "int" here though only nats are supported
  -- Note the breakage here with respect to argument order. We fix this explicitly later.
  show (StrInRe s) = "str.in.re " ++ show s

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
  show (ArrEq i j)       = "array_" ++ show i ++ " == array_" ++ show j
  show (ArrRead i)       = "select array_" ++ show i
  show (KindCast fr to)  = "cast_" ++ show fr ++ "_" ++ show to
  show (Uninterpreted i) = "[uninterpreted] " ++ i
  show (Label s)         = "[label] " ++ s
  show (IEEEFP w)        = show w
  show (PseudoBoolean p) = show p
  show (OverflowOp o)    = show o
  show (StrOp s)         = show s
  show op
    | Just s <- op `lookup` syms = s
    | True                       = error "impossible happened; can't find op!"
    where syms = [ (Plus, "+"), (Times, "*"), (Minus, "-"), (UNeg, "-"), (Abs, "abs")
                 , (Quot, "quot")
                 , (Rem,  "rem")
                 , (Equal, "=="), (NotEqual, "/=")
                 , (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<="), (GreaterEq, ">=")
                 , (Ite, "if_then_else")
                 , (And, "&"), (Or, "|"), (XOr, "^"), (Not, "~")
                 , (Join, "#")
                 ]

-- | Quantifiers: forall or exists. Note that we allow
-- arbitrary nestings.
data Quantifier = ALL | EX deriving Eq

-- | Are there any existential quantifiers?
needsExistentials :: [Quantifier] -> Bool
needsExistentials = (EX `elem`)

-- | A simple type for SBV computations, used mainly for uninterpreted constants.
-- We keep track of the signedness/size of the arguments. A non-function will
-- have just one entry in the list.
newtype SBVType = SBVType [Kind]
             deriving (Eq, Ord)

instance Show SBVType where
  show (SBVType []) = error "SBV: internal error, empty SBVType"
  show (SBVType xs) = intercalate " -> " $ map show xs

-- | A symbolic expression
data SBVExpr = SBVApp !Op ![SW]
             deriving (Eq, Ord)

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
newtype SBVPgm = SBVPgm {pgmAssignments :: S.Seq (SW, SBVExpr)}

-- | 'NamedSymVar' pairs symbolic words and user given/automatically generated names
type NamedSymVar = (SW, String)

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
                             , queryTblArrPreserveIndex :: Maybe (Int, Int)
                             }

-- | A query is a user-guided mechanism to directly communicate and extract results from the solver.
newtype Query a = Query (StateT State IO a)
             deriving (Applicative, Functor, Monad, MonadIO, MonadState State)

instance NFData OptimizeStyle where
   rnf x = x `seq` ()

instance NFData Penalty where
   rnf DefaultPenalty  = ()
   rnf (Penalty p mbs) = rnf p `seq` rnf mbs `seq` ()

instance NFData a => NFData (Objective a) where
   rnf (Minimize          s a)   = rnf s `seq` rnf a `seq` ()
   rnf (Maximize          s a)   = rnf s `seq` rnf a `seq` ()
   rnf (AssertWithPenalty s a p) = rnf s `seq` rnf a `seq` rnf p `seq` ()

-- | Result of running a symbolic computation
data Result = Result { reskinds       :: Set.Set Kind                                     -- ^ kinds used in the program
                     , resTraces      :: [(String, CW)]                                   -- ^ quick-check counter-example information (if any)
                     , resObservables :: [(String, SW)]                                   -- ^ observable expressions (part of the model)
                     , resUISegs      :: [(String, [String])]                             -- ^ uninterpeted code segments
                     , resInputs      :: ([(Quantifier, NamedSymVar)], [NamedSymVar])     -- ^ inputs (possibly existential) + tracker vars
                     , resConsts      :: [(SW, CW)]                                       -- ^ constants
                     , resTables      :: [((Int, Kind, Kind), [SW])]                      -- ^ tables (automatically constructed) (tableno, index-type, result-type) elts
                     , resArrays      :: [(Int, ArrayInfo)]                               -- ^ arrays (user specified)
                     , resUIConsts    :: [(String, SBVType)]                              -- ^ uninterpreted constants
                     , resAxioms      :: [(String, [String])]                             -- ^ axioms
                     , resAsgns       :: SBVPgm                                           -- ^ assignments
                     , resConstraints :: [(Bool, [(String, String)], SW)]                       -- ^ additional constraints (boolean)
                     , resAssertions  :: [(String, Maybe CallStack, SW)]                  -- ^ assertions
                     , resOutputs     :: [SW]                                             -- ^ outputs
                     }

-- Show instance for 'Result'. Only for debugging purposes.
instance Show Result where
  -- If there's nothing interesting going on, just print the constant. Note that the
  -- definiton of interesting here is rather subjective; but essentially if we reduced
  -- the result to a single constant already, without any reference to anything.
  show Result{resConsts=cs, resOutputs=[r]}
    | Just c <- r `lookup` cs
    = show c
  show (Result kinds _ _ cgs is cs ts as uis axs xs cstrs asserts os) = intercalate "\n" $
                   (if null usorts then [] else "SORTS" : map ("  " ++) usorts)
                ++ ["INPUTS"]
                ++ map shn (fst is)
                ++ (if null (snd is) then [] else "TRACKER VARS" : map (shn . (EX,)) (snd is))
                ++ ["CONSTANTS"]
                ++ map shc cs
                ++ ["TABLES"]
                ++ map sht ts
                ++ ["ARRAYS"]
                ++ map sha as
                ++ ["UNINTERPRETED CONSTANTS"]
                ++ map shui uis
                ++ ["USER GIVEN CODE SEGMENTS"]
                ++ concatMap shcg cgs
                ++ ["AXIOMS"]
                ++ map shax axs
                ++ ["DEFINE"]
                ++ map (\(s, e) -> "  " ++ shs s ++ " = " ++ show e) (F.toList (pgmAssignments xs))
                ++ ["CONSTRAINTS"]
                ++ map (("  " ++) . shCstr) cstrs
                ++ ["ASSERTIONS"]
                ++ map (("  "++) . shAssert) asserts
                ++ ["OUTPUTS"]
                ++ sh2 os
    where sh2 :: Show a => [a] -> [String]
          sh2 = map (("  "++) . show)

          usorts = [sh s t | KUserSort s t <- Set.toList kinds]
                   where sh s (Left   _) = s
                         sh s (Right es) = s ++ " (" ++ intercalate ", " es ++ ")"

          shs sw = show sw ++ " :: " ++ show (swKind sw)

          sht ((i, at, rt), es)  = "  Table " ++ show i ++ " : " ++ show at ++ "->" ++ show rt ++ " = " ++ show es

          shc (sw, cw) = "  " ++ show sw ++ " = " ++ show cw

          shcg (s, ss) = ("Variable: " ++ s) : map ("  " ++) ss

          shn (q, (sw, nm)) = "  " ++ ni ++ " :: " ++ show (swKind sw) ++ ex ++ alias
            where ni = show sw
                  ex | q == ALL = ""
                     | True     = ", existential"
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm

          sha (i, (nm, (ai, bi), ctx)) = "  " ++ ni ++ " :: " ++ show ai ++ " -> " ++ show bi ++ alias
                                       ++ "\n     Context: "     ++ show ctx
            where ni = "array_" ++ show i
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm

          shui (nm, t) = "  [uninterpreted] " ++ nm ++ " :: " ++ show t

          shax (nm, ss) = "  -- user defined axiom: " ++ nm ++ "\n  " ++ intercalate "\n  " ss

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
data ArrayContext = ArrayFree (Maybe SW)                   -- ^ A new array, the contents are initialized with the given value, if any
                  | ArrayMutate ArrayIndex SW SW           -- ^ An array created by mutating another array at a given cell
                  | ArrayMerge  SW ArrayIndex ArrayIndex   -- ^ An array created by symbolically merging two other arrays

instance Show ArrayContext where
  show (ArrayFree Nothing)   = " initialized with random elements"
  show (ArrayFree (Just sw)) = " initialized with " ++ show sw
  show (ArrayMutate i a b)   = " cloned from array_" ++ show i ++ " with " ++ show a ++ " :: " ++ show (swKind a) ++ " |-> " ++ show b ++ " :: " ++ show (swKind b)
  show (ArrayMerge  s i j)   = " merged arrays " ++ show i ++ " and " ++ show j ++ " on condition " ++ show s

-- | Expression map, used for hash-consing
type ExprMap = Map.Map SBVExpr SW

-- | Constants are stored in a map, for hash-consing.
type CnstMap = Map.Map CW SW

-- | Kinds used in the program; used for determining the final SMT-Lib logic to pick
type KindSet = Set.Set Kind

-- | Tables generated during a symbolic run
type TableMap = Map.Map (Kind, Kind, [SW]) Int

-- | Representation for symbolic arrays
type ArrayInfo = (String, (Kind, Kind), ArrayContext)

-- | SMT Arrays generated during a symbolic run
type ArrayMap  = IMap.IntMap ArrayInfo

-- | Functional Arrays generated during a symbolic run
type FArrayMap  = IMap.IntMap (SVal -> SVal, IORef (IMap.IntMap SW))

-- | Uninterpreted-constants generated during a symbolic run
type UIMap     = Map.Map String SBVType

-- | Code-segments for Uninterpreted-constants, as given by the user
type CgMap     = Map.Map String [String]

-- | Cached values, implementing sharing
type Cache a   = IMap.IntMap [(StableName (State -> IO a), a)]

-- | Stage of an interactive run
data IStage = ISetup        -- Before we initiate contact.
            | ISafe         -- In the context of a safe/safeWith call
            | IRun          -- After the contact is started

-- | Are we cecking safety
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
data SBVRunMode = SMTMode  IStage Bool SMTConfig -- ^ In regular mode, with a stage. Bool is True if this is SAT.
                | CodeGen                        -- ^ Code generation mode.
                | Concrete                       -- ^ Concrete simulation mode.

-- Show instance for SBVRunMode; debugging purposes only
instance Show SBVRunMode where
   show (SMTMode ISetup True  _) = "Satisfiability setup"
   show (SMTMode ISafe  True  _) = "Safety setup"
   show (SMTMode IRun   True  _) = "Satisfiability"
   show (SMTMode ISetup False _) = "Proof setup"
   show (SMTMode ISafe  False _) = error "ISafe-False is not an expected/supported combination for SBVRunMode!"
   show (SMTMode IRun   False _) = "Proof"
   show CodeGen                  = "Code generation"
   show Concrete                 = "Concrete evaluation"

-- | Is this a CodeGen run? (i.e., generating code)
isCodeGenMode :: State -> IO Bool
isCodeGenMode State{runMode} = do rm <- readIORef runMode
                                  return $ case rm of
                                             Concrete{} -> False
                                             SMTMode{}  -> False
                                             CodeGen    -> True

-- | The state in query mode, i.e., additional context
data IncState = IncState { rNewInps   :: IORef [NamedSymVar]   -- always existential!
                         , rNewKinds  :: IORef KindSet
                         , rNewConsts :: IORef CnstMap
                         , rNewArrs   :: IORef ArrayMap
                         , rNewTbls   :: IORef TableMap
                         , rNewUIs    :: IORef UIMap
                         , rNewAsgns  :: IORef SBVPgm
                         }

-- | Get a new IncState
newIncState :: IO IncState
newIncState = do
        is  <- newIORef []
        ks  <- newIORef Set.empty
        nc  <- newIORef Map.empty
        am  <- newIORef IMap.empty
        tm  <- newIORef Map.empty
        ui  <- newIORef Map.empty
        pgm <- newIORef (SBVPgm S.empty)
        return IncState { rNewInps   = is
                        , rNewKinds  = ks
                        , rNewConsts = nc
                        , rNewArrs   = am
                        , rNewTbls   = tm
                        , rNewUIs    = ui
                        , rNewAsgns  = pgm
                        }

-- | Get a new IncState
withNewIncState :: State -> (State -> IO a) -> IO (IncState, a)
withNewIncState st cont = do
        is <- newIncState
        R.modifyIORef' (rIncState st) (const is)
        r  <- cont st
        finalIncState <- readIORef (rIncState st)
        return (finalIncState, r)

-- | The state of the symbolic interpreter
data State  = State { pathCond     :: SVal                             -- ^ kind KBool
                    , startTime    :: UTCTime
                    , runMode      :: IORef SBVRunMode
                    , rIncState    :: IORef IncState
                    , rCInfo       :: IORef [(String, CW)]
                    , rObservables :: IORef [(String, SW)]
                    , rctr         :: IORef Int
                    , rUsedKinds   :: IORef KindSet
                    , rUsedLbls    :: IORef (Set.Set String)
                    , rinps        :: IORef ([(Quantifier, NamedSymVar)], [NamedSymVar]) -- User defined, and internal existential
                    , rConstraints :: IORef [(Bool, [(String, String)], SW)]
                    , routs        :: IORef [SW]
                    , rtblMap      :: IORef TableMap
                    , spgm         :: IORef SBVPgm
                    , rconstMap    :: IORef CnstMap
                    , rexprMap     :: IORef ExprMap
                    , rArrayMap    :: IORef ArrayMap
                    , rFArrayMap   :: IORef FArrayMap
                    , rUIMap       :: IORef UIMap
                    , rCgMap       :: IORef CgMap
                    , raxioms      :: IORef [(String, [String])]
                    , rSMTOptions  :: IORef [SMTOption]
                    , rOptGoals    :: IORef [Objective (SW, SW)]
                    , rAsserts     :: IORef [(String, Maybe CallStack, SW)]
                    , rSWCache     :: IORef (Cache SW)
                    , rAICache     :: IORef (Cache ArrayIndex)
                    , rFAICache    :: IORef (Cache FArrayIndex)
                    , queryState   :: IORef (Maybe QueryState)
                    }

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
                                         CodeGen    -> False
                                         Concrete{} -> False
                                         SMTMode{}  -> True

-- | The "Symbolic" value. Either a constant (@Left@) or a symbolic
-- value (@Right Cached@). Note that caching is essential for making
-- sure sharing is preserved.
data SVal = SVal !Kind !(Either CW (Cached SW))

instance HasKind SVal where
  kindOf (SVal k _) = k

-- Show instance for 'SVal'. Not particularly "desirable", but will do if needed
-- NB. We do not show the type info on constant KBool values, since there's no
-- implicit "fromBoolean" applied to Booleans in Haskell; and thus a statement
-- of the form "True :: SBool" is just meaningless. (There should be a fromBoolean!)
instance Show SVal where
  show (SVal KBool (Left c))  = showCW False c
  show (SVal k     (Left c))  = showCW False c ++ " :: " ++ show k
  show (SVal k     (Right _)) =         "<symbolic> :: " ++ show k

-- We really don't want an 'Eq' instance for 'SBV' or 'SVal'. As it really makes no sense.
-- But since we do want the 'Bits' instance, we're forced to define equality. See
-- <http://github.com/LeventErkok/sbv/issues/301>. We simply error out.
instance Eq SVal where
  a == b = error $ "Comparing symbolic bit-vectors; Use (.==) instead. Received: " ++ show (a, b)
  a /= b = error $ "Comparing symbolic bit-vectors; Use (./=) instead. Received: " ++ show (a, b)

-- | Things we do not support in interactive mode, at least for now!
noInteractive :: [String] -> a
noInteractive ss = error $ unlines $  ""
                                   :  "*** Data.SBV: Unsupported interactive/query mode feature."
                                   :  map ("***  " ++) ss
                                   ++ ["*** Data.SBV: Please report this as a feature request!"]

-- | Modification of the state, but carefully handling the interactive tasks.
-- Note that the state is always updated regardless of the mode, but we get
-- to also perform extra operation in interactive mode. (Typically error out, but also simply
-- ignore if it has no impact.)
modifyState :: State -> (State -> IORef a) -> (a -> a) -> IO () -> IO ()
modifyState st@State{runMode} field update interactiveUpdate = do
        R.modifyIORef' (field st) update
        rm <- readIORef runMode
        case rm of
          SMTMode IRun _ _ -> interactiveUpdate
          _                -> return ()

-- | Modify the incremental state
modifyIncState  :: State -> (IncState -> IORef a) -> (a -> a) -> IO ()
modifyIncState State{rIncState} field update = do
        incState <- readIORef rIncState
        R.modifyIORef' (field incState) update

-- | Add an observable
recordObservable :: State -> String -> SW -> IO ()
recordObservable st nm sw = modifyState st rObservables ((nm, sw):) (return ())

-- | Increment the variable counter
incrementInternalCounter :: State -> IO Int
incrementInternalCounter st = do ctr <- readIORef (rctr st)
                                 modifyState st rctr (+1) (return ())
                                 return ctr

-- | Uninterpreted constants and functions. An uninterpreted constant is
-- a value that is indexed by its name. The only property the prover assumes
-- about these values are that they are equivalent to themselves; i.e., (for
-- functions) they return the same results when applied to same arguments.
-- We support uninterpreted-functions as a general means of black-box'ing
-- operations that are /irrelevant/ for the purposes of the proof; i.e., when
-- the proofs can be performed without any knowledge about the function itself.
svUninterpreted :: Kind -> String -> Maybe [String] -> [SVal] -> SVal
svUninterpreted k nm code args = SVal k $ Right $ cache result
  where result st = do let ty = SBVType (map kindOf args ++ [k])
                       newUninterpreted st nm ty code
                       sws <- mapM (svToSW st) args
                       mapM_ forceSWArg sws
                       newExpr st k $ SBVApp (Uninterpreted nm) sws

-- | Create a new uninterpreted symbol, possibly with user given code
newUninterpreted :: State -> String -> SBVType -> Maybe [String] -> IO ()
newUninterpreted st nm t mbCode
  | null nm || not enclosed && (not (isAlpha (head nm)) || not (all validChar (tail nm)))
  = error $ "Bad uninterpreted constant name: " ++ show nm ++ ". Must be a valid identifier."
  | True = do uiMap <- readIORef (rUIMap st)
              case nm `Map.lookup` uiMap of
                Just t' -> checkType t' (return ())
                Nothing -> do modifyState st rUIMap (Map.insert nm t)
                                        $ modifyIncState st rNewUIs (\newUIs -> case nm `Map.lookup` newUIs of
                                                                                  Just t' -> checkType t' newUIs
                                                                                  Nothing -> Map.insert nm t newUIs)

                              -- No need to record the code in interactive mode: CodeGen doesn't use interactive
                              when (isJust mbCode) $ modifyState st rCgMap (Map.insert nm (fromJust mbCode)) (return ())
  where checkType t' cont
          | t /= t' = error $  "Uninterpreted constant " ++ show nm ++ " used at incompatible types\n"
                            ++ "      Current type      : " ++ show t ++ "\n"
                            ++ "      Previously used at: " ++ show t'
          | True    = cont


        validChar x = isAlphaNum x || x `elem` "_"
        enclosed    = head nm == '|' && last nm == '|' && length nm > 2 && not (any (`elem` "|\\") (tail (init nm)))

-- | Add a new sAssert based constraint
addAssertion :: State -> Maybe CallStack -> String -> SW -> IO ()
addAssertion st cs msg cond = modifyState st rAsserts ((msg, cs, cond):)
                                        $ noInteractive [ "Named assertions (sAssert):"
                                                        , "  Tag: " ++ msg
                                                        , "  Loc: " ++ maybe "Unknown" show cs
                                                        ]

-- | Create an internal variable, which acts as an input but isn't visible to the user.
-- Such variables are existentially quantified in a SAT context, and universally quantified
-- in a proof context.
internalVariable :: State -> Kind -> IO SW
internalVariable st k = do (sw, nm) <- newSW st k
                           rm <- readIORef (runMode st)
                           let q = case rm of
                                     SMTMode    _ True  _ -> EX
                                     SMTMode    _ False _ -> ALL
                                     CodeGen              -> ALL
                                     Concrete{}           -> ALL
                           modifyState st rinps (first ((:) (q, (sw, "__internal_sbv_" ++ nm))))
                                     $ noInteractive [ "Internal variable creation:"
                                                     , "  Named: " ++ nm
                                                     ]
                           return sw
{-# INLINE internalVariable #-}

-- | Create a new SW
newSW :: State -> Kind -> IO (SW, String)
newSW st k = do ctr <- incrementInternalCounter st
                let sw = SW k (NodeId ctr)
                registerKind st k
                return (sw, 's' : show ctr)
{-# INLINE newSW #-}

-- | Register a new kind with the system, used for uninterpreted sorts.
-- NB: Is it safe to have new kinds in query mode? It could be that
-- the new kind might introduce a constraint that effects the logic. For
-- instance, if we're seeing 'Double' for the first time and using a BV
-- logic, then things would fall apart. But this should be rare, and hopefully
-- the 'success' checking mechanism will catch the rare cases where this
-- is an issue. In either case, the user can always arrange for the right
-- logic by calling 'setLogic' appropriately, so it seems safe to just
-- allow for this.
registerKind :: State -> Kind -> IO ()
registerKind st k
  | KUserSort sortName _ <- k, map toLower sortName `elem` smtLibReservedNames
  = error $ "SBV: " ++ show sortName ++ " is a reserved sort; please use a different name."
  | True
  = do ks <- readIORef (rUsedKinds st)
       unless (k `Set.member` ks) $ modifyState st rUsedKinds (Set.insert k)
                                              $ modifyIncState st rNewKinds (Set.insert k)

-- | Register a new label with the system, making sure they are unique and have no '|'s in them
registerLabel :: String -> State -> String -> IO ()
registerLabel whence st nm
  | map toLower nm `elem` smtLibReservedNames
  = err "is a reserved string; please use a different name."
  | '|' `elem` nm
  = err "contains the character `|', which is not allowed!"
  | '\\' `elem` nm
  = err "contains the character `\', which is not allowed!"
  | True
  = do old <- readIORef $ rUsedLbls st
       if nm `Set.member` old
          then err "is used multiple times. Please do not use duplicate names!"
          else modifyState st rUsedLbls (Set.insert nm) (return ())

  where err w = error $ "SBV (" ++ whence ++ "): " ++ show nm ++ " " ++ w

-- | Create a new constant; hash-cons as necessary
newConst :: State -> CW -> IO SW
newConst st c = do
  constMap <- readIORef (rconstMap st)
  case c `Map.lookup` constMap of
    Just sw -> return sw
    Nothing -> do let k = kindOf c
                  (sw, _) <- newSW st k
                  let ins = Map.insert c sw
                  modifyState st rconstMap ins $ modifyIncState st rNewConsts ins
                  return sw
{-# INLINE newConst #-}

-- | Create a new table; hash-cons as necessary
getTableIndex :: State -> Kind -> Kind -> [SW] -> IO Int
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
newExpr :: State -> Kind -> SBVExpr -> IO SW
newExpr st k app = do
   let e = reorder app
   exprMap <- readIORef (rexprMap st)
   case e `Map.lookup` exprMap of
     Just sw -> return sw
     Nothing -> do (sw, _) <- newSW st k
                   let append (SBVPgm xs) = SBVPgm (xs S.|> (sw, e))
                   modifyState st spgm append $ modifyIncState st rNewAsgns append
                   modifyState st rexprMap (Map.insert e sw) (return ())
                   return sw
{-# INLINE newExpr #-}

-- | Convert a symbolic value to a symbolic-word
svToSW :: State -> SVal -> IO SW
svToSW st (SVal _ (Left c))  = newConst st c
svToSW st (SVal _ (Right f)) = uncache f st

-- | Convert a symbolic value to an SW, inside the Symbolic monad
svToSymSW :: SVal -> Symbolic SW
svToSymSW sbv = do st <- ask
                   liftIO $ svToSW st sbv

-------------------------------------------------------------------------
-- * Symbolic Computations
-------------------------------------------------------------------------
-- | A Symbolic computation. Represented by a reader monad carrying the
-- state of the computation, layered on top of IO for creating unique
-- references to hold onto intermediate results.
newtype Symbolic a = Symbolic (ReaderT State IO a)
                   deriving (Applicative, Functor, Monad, MonadIO, MonadReader State)

-- | Create a symbolic value, based on the quantifier we have. If an
-- explicit quantifier is given, we just use that. If not, then we
-- pick the quantifier appropriately based on the run-mode.
-- @randomCW@ is used for generating random values for this variable
-- when used for 'quickCheck' or 'genTest' purposes.
svMkSymVar :: Maybe Quantifier -> Kind -> Maybe String -> State -> IO SVal
svMkSymVar = svMkSymVarGen False

-- | Create an existentially quantified tracker variable
svMkTrackerVar :: Kind -> String -> State -> IO SVal
svMkTrackerVar k nm = svMkSymVarGen True (Just EX) k (Just nm)

-- | Create an N-bit symbolic unsigned named variable
sWordN :: Int -> String -> Symbolic SVal
sWordN w nm = ask >>= liftIO . svMkSymVar Nothing (KBounded False w) (Just nm)

-- | Create an N-bit symbolic unsigned unnamed variable
sWordN_ :: Int -> Symbolic SVal
sWordN_ w = ask >>= liftIO . svMkSymVar Nothing (KBounded False w) Nothing

-- | Create an N-bit symbolic signed named variable
sIntN :: Int -> String -> Symbolic SVal
sIntN w nm = ask >>= liftIO . svMkSymVar Nothing (KBounded True w) (Just nm)

-- | Create an N-bit symbolic signed unnamed variable
sIntN_ :: Int -> Symbolic SVal
sIntN_ w = ask >>= liftIO . svMkSymVar Nothing (KBounded True w) Nothing

-- | Create a symbolic value, based on the quantifier we have. If an
-- explicit quantifier is given, we just use that. If not, then we
-- pick the quantifier appropriately based on the run-mode.
-- @randomCW@ is used for generating random values for this variable
-- when used for 'quickCheck' or 'genTest' purposes.
svMkSymVarGen :: Bool -> Maybe Quantifier -> Kind -> Maybe String -> State -> IO SVal
svMkSymVarGen isTracker mbQ k mbNm st = do
        rm <- readIORef (runMode st)

        let varInfo = case mbNm of
                        Nothing -> ", of type " ++ show k
                        Just nm -> ", while defining " ++ nm ++ " :: " ++ show k

            disallow what  = error $ "Data.SBV: Unsupported: " ++ what ++ varInfo ++ " in mode: " ++ show rm

            noUI cont
              | isUninterpreted k  = disallow "Uninterpreted sorts"
              | True               = cont

            mkS q = do (sw, internalName) <- newSW st k
                       let nm = fromMaybe internalName mbNm
                       introduceUserName st isTracker nm k q sw

            mkC   = do cw <- randomCW k
                       do registerKind st k
                          modifyState st rCInfo ((fromMaybe "_" mbNm, cw):) (return ())
                       return $ SVal k (Left cw)

        case (mbQ, rm) of
          (Just q,  SMTMode{}        ) -> mkS q
          (Nothing, SMTMode _ isSAT _) -> mkS (if isSAT then EX else ALL)

          (Just EX, CodeGen{})         -> disallow "Existentially quantified variables"
          (_      , CodeGen)           -> noUI $ mkS ALL  -- code generation, pick universal

          (Just EX,  Concrete{})       -> disallow "Existentially quantified variables"
          (_      ,  Concrete{})       -> noUI mkC

-- | Introduce a new user name. We die if repeated.
introduceUserName :: State -> Bool -> String -> Kind -> Quantifier -> SW -> IO SVal
introduceUserName st isTracker nm k q sw = do
        (is, ints) <- readIORef (rinps st)
        if nm `elem` [n | (_, (_, n)) <- is] ++ [n | (_, n) <- ints]
           then error $ "SBV: Repeated user given name: " ++ show nm ++ ". Please use unique names."
           else if isTracker && q == ALL
                then error $ "SBV: Impossible happened! A universally quantified tracker variable is being introduced: " ++ show nm
                else do let newInp olds = case q of
                                           EX  -> (sw, nm) : olds
                                           ALL -> noInteractive [ "Adding a new universally quantified variable: "
                                                                , "  Name      : " ++ show nm
                                                                , "  Kind      : " ++ show k
                                                                , "  Quantifier: Universal"
                                                                , "  Node      : " ++ show sw
                                                                , "Only existential variables are supported in query mode."
                                                                ]
                        if isTracker
                           then modifyState st rinps (second ((:) (sw, nm)))
                                          $ noInteractive ["Adding a new tracker variable in interactive mode: " ++ show nm]
                           else modifyState st rinps (first ((:) (q, (sw, nm))))
                                          $ modifyIncState st rNewInps newInp
                        return $ SVal k $ Right $ cache (const (return sw))

-- | Add a user specified axiom to the generated SMT-Lib file. The first argument is a mere
-- string, use for commenting purposes. The second argument is intended to hold the multiple-lines
-- of the axiom text as expressed in SMT-Lib notation. Note that we perform no checks on the axiom
-- itself, to see whether it's actually well-formed or is sensical by any means.
-- A separate formalization of SMT-Lib would be very useful here.
addAxiom :: String -> [String] -> Symbolic ()
addAxiom nm ax = do
        st <- ask
        liftIO $ modifyState st raxioms ((nm, ax) :)
                           $ noInteractive [ "Adding a new axiom:"
                                           , "  Named: " ++ show nm
                                           , "  Axiom: " ++ unlines ax
                                           ]

-- | Run a symbolic computation, and return a extra value paired up with the 'Result'
runSymbolic :: SBVRunMode -> Symbolic a -> IO (a, Result)
runSymbolic currentRunMode (Symbolic c) = do
   currTime  <- getCurrentTime
   rm        <- newIORef currentRunMode
   ctr       <- newIORef (-2) -- start from -2; False and True will always occupy the first two elements
   cInfo     <- newIORef []
   observes  <- newIORef []
   pgm       <- newIORef (SBVPgm S.empty)
   emap      <- newIORef Map.empty
   cmap      <- newIORef Map.empty
   inps      <- newIORef ([], [])
   outs      <- newIORef []
   tables    <- newIORef Map.empty
   arrays    <- newIORef IMap.empty
   fArrays   <- newIORef IMap.empty
   uis       <- newIORef Map.empty
   cgs       <- newIORef Map.empty
   axioms    <- newIORef []
   swCache   <- newIORef IMap.empty
   aiCache   <- newIORef IMap.empty
   faiCache  <- newIORef IMap.empty
   usedKinds <- newIORef Set.empty
   usedLbls  <- newIORef Set.empty
   cstrs     <- newIORef []
   smtOpts   <- newIORef []
   optGoals  <- newIORef []
   asserts   <- newIORef []
   istate    <- newIORef =<< newIncState
   qstate    <- newIORef Nothing
   let st = State { runMode      = rm
                  , startTime    = currTime
                  , pathCond     = SVal KBool (Left trueCW)
                  , rIncState    = istate
                  , rCInfo       = cInfo
                  , rObservables = observes
                  , rctr         = ctr
                  , rUsedKinds   = usedKinds
                  , rUsedLbls    = usedLbls
                  , rinps        = inps
                  , routs        = outs
                  , rtblMap      = tables
                  , spgm         = pgm
                  , rconstMap    = cmap
                  , rArrayMap    = arrays
                  , rFArrayMap   = fArrays
                  , rexprMap     = emap
                  , rUIMap       = uis
                  , rCgMap       = cgs
                  , raxioms      = axioms
                  , rSWCache     = swCache
                  , rAICache     = aiCache
                  , rFAICache    = faiCache
                  , rConstraints = cstrs
                  , rSMTOptions  = smtOpts
                  , rOptGoals    = optGoals
                  , rAsserts     = asserts
                  , queryState   = qstate
                  }
   _ <- newConst st falseCW -- s(-2) == falseSW
   _ <- newConst st trueCW  -- s(-1) == trueSW
   r <- runReaderT c st
   res <- extractSymbolicSimulationState st

   -- Clean-up after ourselves
   qs <- readIORef qstate
   case qs of
     Nothing                         -> return ()
     Just QueryState{queryTerminate} -> queryTerminate

   return (r, res)

-- | Grab the program from a running symbolic simulation state.
extractSymbolicSimulationState :: State -> IO Result
extractSymbolicSimulationState st@State{ spgm=pgm, rinps=inps, routs=outs, rtblMap=tables, rArrayMap=arrays, rUIMap=uis, raxioms=axioms
                                       , rAsserts=asserts, rUsedKinds=usedKinds, rCgMap=cgs, rCInfo=cInfo, rConstraints=cstrs
                                       , rObservables=observes
                                       } = do
   SBVPgm rpgm  <- readIORef pgm
   inpsO <- (reverse *** reverse) <$> readIORef inps
   outsO <- reverse <$> readIORef outs

   let swap  (a, b)              = (b, a)
       cmp   (a, _) (b, _)       = a `compare` b
       arrange (i, (at, rt, es)) = ((i, at, rt), es)

   cnsts <- sortBy cmp . map swap . Map.toList <$> readIORef (rconstMap st)
   tbls  <- map arrange . sortBy cmp . map swap . Map.toList <$> readIORef tables
   arrs  <- IMap.toAscList <$> readIORef arrays
   unint <- Map.toList <$> readIORef uis
   axs   <- reverse <$> readIORef axioms
   knds  <- readIORef usedKinds
   cgMap <- Map.toList <$> readIORef cgs

   traceVals   <- reverse <$> readIORef cInfo
   observables <- reverse <$> readIORef observes
   extraCstrs  <- reverse <$> readIORef cstrs
   assertions  <- reverse <$> readIORef asserts

   return $ Result knds traceVals observables cgMap inpsO cnsts tbls arrs unint axs (SBVPgm rpgm) extraCstrs assertions outsO

-- | Add a new option
addNewSMTOption :: SMTOption -> Symbolic ()
addNewSMTOption o =  do st <- ask
                        liftIO $ modifyState st rSMTOptions (o:) (return ())

-- | Handling constraints
imposeConstraint :: Bool -> [(String, String)] -> SVal -> Symbolic ()
imposeConstraint isSoft attrs c = do st <- ask
                                     rm <- liftIO $ readIORef (runMode st)
                                     case rm of
                                       CodeGen -> error "SBV: constraints are not allowed in code-generation"
                                       _       -> liftIO $ do mapM_ (registerLabel "Constraint" st) [nm | (":named",  nm) <- attrs]
                                                              internalConstraint st isSoft attrs c

-- | Require a boolean condition to be true in the state. Only used for internal purposes.
internalConstraint :: State -> Bool -> [(String, String)] -> SVal -> IO ()
internalConstraint st isSoft attrs b = do v <- svToSW st b
                                          modifyState st rConstraints ((isSoft, attrs, v):)
                                                    $ noInteractive [ "Adding an internal " ++ soft ++ "constraint:"
                                                                    , "  Named: " ++ fromMaybe "<unnamed>" (listToMaybe [nm | (":named", nm) <- attrs])
                                                                    ]
    where soft | isSoft = "soft-"
               | True   = ""

-- | Add an optimization goal
addSValOptGoal :: Objective SVal -> Symbolic ()
addSValOptGoal obj = do st <- ask

                        -- create the tracking variable here for the metric
                        let mkGoal nm orig = liftIO $ do origSW  <- svToSW st orig
                                                         track   <- svMkTrackerVar (kindOf orig) nm st
                                                         trackSW <- svToSW st track
                                                         return (origSW, trackSW)

                        let walk (Minimize          nm v)     = Minimize nm                     <$> mkGoal nm v
                            walk (Maximize          nm v)     = Maximize nm                     <$> mkGoal nm v
                            walk (AssertWithPenalty nm v mbP) = flip (AssertWithPenalty nm) mbP <$> mkGoal nm v

                        obj' <- walk obj
                        liftIO $ modifyState st rOptGoals (obj' :)
                                           $ noInteractive [ "Adding an optimization objective:"
                                                           , "  Objective: " ++ show obj
                                                           ]

-- | Mark an interim result as an output. Useful when constructing Symbolic programs
-- that return multiple values, or when the result is programmatically computed.
outputSVal :: SVal -> Symbolic ()
outputSVal (SVal _ (Left c)) = do
  st <- ask
  sw <- liftIO $ newConst st c
  liftIO $ modifyState st routs (sw:) (return ())
outputSVal (SVal _ (Right f)) = do
  st <- ask
  sw <- liftIO $ uncache f st
  liftIO $ modifyState st routs (sw:) (return ())

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
-- See Andy Gill's type-safe obervable sharing trick for the inspiration behind
-- this technique: <http://ku-fpg.github.io/files/Gill-09-TypeSafeReification.pdf>
--
-- Note that this is *not* a general memo utility!
newtype Cached a = Cached (State -> IO a)

-- | Cache a state-based computation
cache :: (State -> IO a) -> Cached a
cache = Cached

-- | Uncache a previously cached computation
uncache :: Cached SW -> State -> IO SW
uncache = uncacheGen rSWCache

-- | An SMT array index is simply an int value
newtype ArrayIndex = ArrayIndex { unArrayIndex :: Int } deriving (Eq, Ord)

-- | We simply show indexes as the underlying integer
instance Show ArrayIndex where
  show (ArrayIndex i) = show i

-- | A functional array index is simply an int value
newtype FArrayIndex = FArrayIndex { unFArrayIndex :: Int } deriving (Eq, Ord)

-- | We simply show indexes as the underlying integer
instance Show FArrayIndex where
  show (FArrayIndex i) = show i

-- | Uncache, retrieving SMT array indexes
uncacheAI :: Cached ArrayIndex -> State -> IO ArrayIndex
uncacheAI = uncacheGen rAICache

-- | Uncache, retrieving Functional array indexes
uncacheFAI :: Cached FArrayIndex -> State -> IO FArrayIndex
uncacheFAI = uncacheGen rFAICache

-- | Generic uncaching. Note that this is entirely safe, since we do it in the IO monad.
uncacheGen :: (State -> IORef (Cache a)) -> Cached a -> State -> IO a
uncacheGen getCache (Cached f) st = do
        let rCache = getCache st
        stored <- readIORef rCache
        sn <- f `seq` makeStableName f
        let h = hashStableName sn
        case maybe Nothing (sn `lookup`) (h `IMap.lookup` stored) of
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

-- | Representation of an SMT-Lib program. In between pre and post goes the refuted models
data SMTLibPgm = SMTLibPgm SMTLibVersion [String]

instance NFData SMTLibVersion where rnf a               = a `seq` ()
instance NFData SMTLibPgm     where rnf (SMTLibPgm v p) = rnf v `seq` rnf p `seq` ()

instance Show SMTLibPgm where
  show (SMTLibPgm _ pre) = intercalate "\n" pre

-- Other Technicalities..
instance NFData CW where
  rnf (CW x y) = x `seq` y `seq` ()

instance NFData GeneralizedCW where
  rnf (ExtendedCW e) = e `seq` ()
  rnf (RegularCW  c) = c `seq` ()

#if MIN_VERSION_base(4,9,0)
#else
-- Can't really force this, but not a big deal
instance NFData CallStack where
  rnf _ = ()
#endif

instance NFData Result where
  rnf (Result kindInfo qcInfo obs cgs inps consts tbls arrs uis axs pgm cstr asserts outs)
        = rnf kindInfo `seq` rnf qcInfo  `seq` rnf obs    `seq` rnf cgs
                       `seq` rnf inps    `seq` rnf consts `seq` rnf tbls
                       `seq` rnf arrs    `seq` rnf uis    `seq` rnf axs 
                       `seq` rnf pgm     `seq` rnf cstr   `seq` rnf asserts
                       `seq` rnf outs
instance NFData Kind         where rnf a          = seq a ()
instance NFData ArrayContext where rnf a          = seq a ()
instance NFData SW           where rnf a          = seq a ()
instance NFData SBVExpr      where rnf a          = seq a ()
instance NFData Quantifier   where rnf a          = seq a ()
instance NFData SBVType      where rnf a          = seq a ()
instance NFData SBVPgm       where rnf a          = seq a ()
instance NFData (Cached a)   where rnf (Cached f) = f `seq` ()
instance NFData SVal         where rnf (SVal x y) = rnf x `seq` rnf y `seq` ()

instance NFData SMTResult where
  rnf Unsatisfiable{}      = ()
  rnf (Satisfiable _   xs) = rnf xs `seq` ()
  rnf (SatExtField _   xs) = rnf xs `seq` ()
  rnf (Unknown _       xs) = rnf xs `seq` ()
  rnf (ProofError _    xs) = rnf xs `seq` ()

instance NFData SMTModel where
  rnf (SMTModel objs assocs) = rnf objs `seq` rnf assocs `seq` ()

instance NFData SMTScript where
  rnf (SMTScript b m) = rnf b `seq` rnf m `seq` ()

-- | Translation tricks needed for specific capabilities afforded by each solver
data SolverCapabilities = SolverCapabilities {
         supportsQuantifiers        :: Bool    -- ^ Support for SMT-Lib2 style quantifiers?
       , supportsUninterpretedSorts :: Bool    -- ^ Support for SMT-Lib2 style uninterpreted-sorts
       , supportsUnboundedInts      :: Bool    -- ^ Support for unbounded integers?
       , supportsReals              :: Bool    -- ^ Support for reals?
       , supportsApproxReals        :: Bool    -- ^ Supports printing of approximations of reals?
       , supportsIEEE754            :: Bool    -- ^ Support for floating point numbers?
       , supportsOptimization       :: Bool    -- ^ Support for optimization routines?
       , supportsPseudoBooleans     :: Bool    -- ^ Support for pseudo-boolean operations?
       , supportsCustomQueries      :: Bool    -- ^ Support for interactive queries per SMT-Lib?
       , supportsGlobalDecls        :: Bool    -- ^ Support for global decls, needed for push-pop.
       }

-- | Rounding mode to be used for the IEEE floating-point operations.
-- Note that Haskell's default is 'RoundNearestTiesToEven'. If you use
-- a different rounding mode, then the counter-examples you get may not
-- match what you observe in Haskell.
data RoundingMode = RoundNearestTiesToEven  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the even number.
                                            -- (In this context, /even/ means the lowest-order bit is zero.)
                  | RoundNearestTiesToAway  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the number further away from 0.
                                            -- (That is, for positive values, pick the greater; for negative values, pick the smaller.)
                  | RoundTowardPositive     -- ^ Round towards positive infinity. (Also known as rounding-up or ceiling.)
                  | RoundTowardNegative     -- ^ Round towards negative infinity. (Also known as rounding-down or floor.)
                  | RoundTowardZero         -- ^ Round towards zero. (Also known as truncation.)
                  deriving (Eq, Ord, Show, Read, G.Data, Bounded, Enum)

-- | 'RoundingMode' kind
instance HasKind RoundingMode

-- | Solver configuration. See also 'z3', 'yices', 'cvc4', 'boolector', 'mathSAT', etc. which are instantiations of this type for those solvers, with
-- reasonable defaults. In particular, custom configuration can be created by varying those values. (Such as @z3{verbose=True}@.)
--
-- Most fields are self explanatory. The notion of precision for printing algebraic reals stems from the fact that such values does
-- not necessarily have finite decimal representations, and hence we have to stop printing at some depth. It is important to
-- emphasize that such values always have infinite precision internally. The issue is merely with how we print such an infinite
-- precision value on the screen. The field 'printRealPrec' controls the printing precision, by specifying the number of digits after
-- the decimal point. The default value is 16, but it can be set to any positive integer.
--
-- When printing, SBV will add the suffix @...@ at the and of a real-value, if the given bound is not sufficient to represent the real-value
-- exactly. Otherwise, the number will be written out in standard decimal notation. Note that SBV will always print the whole value if it
-- is precise (i.e., if it fits in a finite number of digits), regardless of the precision limit. The limit only applies if the representation
-- of the real value is not finite, i.e., if it is not rational.
--
-- The 'printBase' field can be used to print numbers in base 2, 10, or 16. If base 2 or 16 is used, then floating-point values will
-- be printed in their internal memory-layout format as well, which can come in handy for bit-precise analysis.
data SMTConfig = SMTConfig {
         verbose             :: Bool           -- ^ Debug mode
       , timing              :: Timing         -- ^ Print timing information on how long different phases took (construction, solving, etc.)
       , printBase           :: Int            -- ^ Print integral literals in this base (2, 10, and 16 are supported.)
       , printRealPrec       :: Int            -- ^ Print algebraic real values with this precision. (SReal, default: 16)
       , satCmd              :: String         -- ^ Usually "(check-sat)". However, users might tweak it based on solver characteristics.
       , allSatMaxModelCount :: Maybe Int      -- ^ In an allSat call, return at most this many models. If nothing, return all.
       , isNonModelVar       :: String -> Bool -- ^ When constructing a model, ignore variables whose name satisfy this predicate. (Default: (const False), i.e., don't ignore anything)
       , transcript          :: Maybe FilePath -- ^ If Just, the entire interaction will be recorded as a playable file (for debugging purposes mostly)
       , smtLibVersion       :: SMTLibVersion  -- ^ What version of SMT-lib we use for the tool
       , solver              :: SMTSolver      -- ^ The actual SMT solver.
       , roundingMode        :: RoundingMode   -- ^ Rounding mode to use for floating-point conversions
       , solverSetOptions    :: [SMTOption]    -- ^ Options to set as we start the solver
       , ignoreExitCode      :: Bool           -- ^ If true, we shall ignore the exit code upon exit. Otherwise we require ExitSuccess.
       , redirectVerbose     :: Maybe FilePath -- ^ Redirect the verbose output to this file if given. If Nothing, stdout is implied.
       }

-- We're just seq'ing top-level here, it shouldn't really matter. (i.e., no need to go deeper.)
instance NFData SMTConfig where
  rnf SMTConfig{} = ()

-- | A model, as returned by a solver
data SMTModel = SMTModel {
        modelObjectives :: [(String, GeneralizedCW)]  -- ^ Mapping of symbolic values to objective values.
     ,  modelAssocs     :: [(String, CW)]             -- ^ Mapping of symbolic values to constants.
     }
     deriving Show

-- | The result of an SMT solver call. Each constructor is tagged with
-- the 'SMTConfig' that created it so that further tools can inspect it
-- and build layers of results, if needed. For ordinary uses of the library,
-- this type should not be needed, instead use the accessor functions on
-- it. (Custom Show instances and model extractors.)
data SMTResult = Unsatisfiable SMTConfig (Maybe [String]) -- ^ Unsatisfiable. If unsat-cores are enabled, they will be returned in the second parameter.
               | Satisfiable   SMTConfig SMTModel         -- ^ Satisfiable with model
               | SatExtField   SMTConfig SMTModel         -- ^ Prover returned a model, but in an extension field containing Infinite/epsilon
               | Unknown       SMTConfig SMTReasonUnknown -- ^ Prover returned unknown, with the given reason
               | ProofError    SMTConfig [String]         -- ^ Prover errored out

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
data Solver = Z3
            | Yices
            | Boolector
            | CVC4
            | MathSAT
            | ABC
            deriving (Show, Enum, Bounded)

-- | An SMT solver
data SMTSolver = SMTSolver {
         name           :: Solver                -- ^ The solver in use
       , executable     :: String                -- ^ The path to its executable
       , options        :: SMTConfig -> [String] -- ^ Options to provide to the solver
       , engine         :: SMTEngine             -- ^ The solver engine, responsible for interpreting solver output
       , capabilities   :: SolverCapabilities    -- ^ Various capabilities of the solver
       }

-- | Query execution context
data QueryContext = QueryInternal       -- ^ Triggered from inside SBV
                  | QueryExternal       -- ^ Triggered from user code

{-# ANN type FPOp ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN type PBOp ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN type OvOp ("HLint: ignore Use camelCase" :: String) #-}
