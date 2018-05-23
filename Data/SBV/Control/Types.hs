-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control.Types
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Types related to interactive queries
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE DeriveAnyClass #-}

module Data.SBV.Control.Types (
       CheckSatResult(..)
     , Logic(..)
     , SMTOption(..), isStartModeOption, setSMTOption
     , SMTInfoFlag(..)
     , SMTErrorBehavior(..)
     , SMTReasonUnknown(..)
     , SMTInfoResponse(..)
     ) where

import Generics.Deriving.Base (Generic)
import Generics.Deriving.Show (GShow, gshow)

import Control.DeepSeq (NFData(..))

-- | Result of a 'checkSat' or 'checkSatAssuming' call.
data CheckSatResult = Sat           -- ^ Satisfiable: A model is available, which can be queried with 'Data.SBV.Control.getValue'.
                    | Unsat         -- ^ Unsatisfiable: No model is available. Unsat cores might be obtained via 'Data.SBV.Control.getUnsatCore'.
                    | Unk           -- ^ Unknown: Use 'Data.SBV.Control.getUnknownReason' to obtain an explanation why this might be the case.
                    deriving (Eq, Show)

-- | Collectable information from the solver.
data SMTInfoFlag = AllStatistics
                 | AssertionStackLevels
                 | Authors
                 | ErrorBehavior
                 | Name
                 | ReasonUnknown
                 | Version
                 | InfoKeyword String

-- | Behavior of the solver for errors.
data SMTErrorBehavior = ErrorImmediateExit
                      | ErrorContinuedExecution
                      deriving Show

-- | Reason for reporting unknown.
data SMTReasonUnknown = UnknownMemOut
                      | UnknownIncomplete
                      | UnknownTimeOut
                      | UnknownOther      String
                      deriving (Generic, NFData)

-- | Show instance for unknown
instance Show SMTReasonUnknown where
  show UnknownMemOut     = "memout"
  show UnknownIncomplete = "incomplete"
  show UnknownTimeOut    = "timeout"
  show (UnknownOther s)  = s

-- | Collectable information from the solver.
data SMTInfoResponse = Resp_Unsupported
                     | Resp_AllStatistics        [(String, String)]
                     | Resp_AssertionStackLevels Integer
                     | Resp_Authors              [String]
                     | Resp_Error                SMTErrorBehavior
                     | Resp_Name                 String
                     | Resp_ReasonUnknown        SMTReasonUnknown
                     | Resp_Version              String
                     | Resp_InfoKeyword          String [String]
                     deriving Show

-- Show instance for SMTInfoFlag maintains smt-lib format per the SMTLib2 standard document.
instance Show SMTInfoFlag where
  show AllStatistics        = ":all-statistics"
  show AssertionStackLevels = ":assertion-stack-levels"
  show Authors              = ":authors"
  show ErrorBehavior        = ":error-behavior"
  show Name                 = ":name"
  show ReasonUnknown        = ":reason-unknown"
  show Version              = ":version"
  show (InfoKeyword s)      = s

-- | Option values that can be set in the solver, following the SMTLib specification <http://smtlib.cs.uiowa.edu/language.shtml>.
--
-- Note that not all solvers may support all of these!
--
-- Furthermore, SBV doesn't support the following options allowed by SMTLib.
--
--    * @:interactive-mode@                (Deprecated in SMTLib, use 'ProduceAssertions' instead.)
--    * @:print-success@                   (SBV critically needs this to be True in query mode.)
--    * @:produce-models@                  (SBV always sets this option so it can extract models.)
--    * @:regular-output-channel@          (SBV always requires regular output to come on stdout for query purposes.)
--    * @:global-declarations@             (SBV always uses global declarations since definitions are accumulative.)
--
-- Note that 'SetLogic' and 'SetInfo' are, strictly speaking, not SMTLib options. However, we treat it as such here
-- uniformly, as it fits better with how options work.
data SMTOption = DiagnosticOutputChannel   FilePath
               | ProduceAssertions         Bool
               | ProduceAssignments        Bool
               | ProduceProofs             Bool
               | ProduceInterpolants       Bool
               | ProduceUnsatAssumptions   Bool
               | ProduceUnsatCores         Bool
               | RandomSeed                Integer
               | ReproducibleResourceLimit Integer
               | SMTVerbosity              Integer
               | OptionKeyword             String  [String]
               | SetLogic                  Logic
               | SetInfo                   String  [String]
               deriving (Show, Generic, NFData)

-- | Can this command only be run at the very beginning? If 'True' then
-- we will reject setting these options in the query mode. Note that this
-- classification follows the SMTLib document.
isStartModeOption :: SMTOption -> Bool
isStartModeOption DiagnosticOutputChannel{}   = False
isStartModeOption ProduceAssertions{}         = True
isStartModeOption ProduceAssignments{}        = True
isStartModeOption ProduceProofs{}             = True
isStartModeOption ProduceInterpolants{}       = True
isStartModeOption ProduceUnsatAssumptions{}   = True
isStartModeOption ProduceUnsatCores{}         = True
isStartModeOption RandomSeed{}                = True
isStartModeOption ReproducibleResourceLimit{} = False
isStartModeOption SMTVerbosity{}              = False
isStartModeOption OptionKeyword{}             = True  -- Conservative.
isStartModeOption SetLogic{}                  = True
isStartModeOption SetInfo{}                   = False

-- SMTLib's True/False is spelled differently than Haskell's.
smtBool :: Bool -> String
smtBool True  = "true"
smtBool False = "false"

-- | Translate an option setting to SMTLib. Note the SetLogic/SetInfo discrepancy.
setSMTOption :: SMTOption -> String
setSMTOption = cvt
  where cvt (DiagnosticOutputChannel   f) = opt   [":diagnostic-output-channel",   show f]
        cvt (ProduceAssertions         b) = opt   [":produce-assertions",          smtBool b]
        cvt (ProduceAssignments        b) = opt   [":produce-assignments",         smtBool b]
        cvt (ProduceProofs             b) = opt   [":produce-proofs",              smtBool b]
        cvt (ProduceInterpolants       b) = opt   [":produce-interpolants",        smtBool b]
        cvt (ProduceUnsatAssumptions   b) = opt   [":produce-unsat-assumptions",   smtBool b]
        cvt (ProduceUnsatCores         b) = opt   [":produce-unsat-cores",         smtBool b]
        cvt (RandomSeed                i) = opt   [":random-seed",                 show i]
        cvt (ReproducibleResourceLimit i) = opt   [":reproducible-resource-limit", show i]
        cvt (SMTVerbosity              i) = opt   [":verbosity",                   show i]
        cvt (OptionKeyword          k as) = opt   (k : as)
        cvt (SetLogic                  l) = logic l
        cvt (SetInfo                k as) = info  (k : as)

        opt   xs = "(set-option " ++ unwords xs ++ ")"
        info  xs = "(set-info "   ++ unwords xs ++ ")"

        logic Logic_NONE = "; NB. not setting the logic per user request of Logic_NONE"
        logic l          = "(set-logic " ++ show l ++ ")"

-- | SMT-Lib logics. If left unspecified SBV will pick the logic based on what it determines is needed. However, the
-- user can override this choice using a call to 'setLogic' This is especially handy if one is experimenting with custom
-- logics that might be supported on new solvers. See <http://smtlib.cs.uiowa.edu/logics.shtml> for the official list.
data Logic
  = AUFLIA             -- ^ Formulas over the theory of linear integer arithmetic and arrays extended with free sort and function symbols but restricted to arrays with integer indices and values.
  | AUFLIRA            -- ^ Linear formulas with free sort and function symbols over one- and two-dimentional arrays of integer index and real value.
  | AUFNIRA            -- ^ Formulas with free function and predicate symbols over a theory of arrays of arrays of integer index and real value.
  | LRA                -- ^ Linear formulas in linear real arithmetic.
  | QF_ABV             -- ^ Quantifier-free formulas over the theory of bitvectors and bitvector arrays.
  | QF_AUFBV           -- ^ Quantifier-free formulas over the theory of bitvectors and bitvector arrays extended with free sort and function symbols.
  | QF_AUFLIA          -- ^ Quantifier-free linear formulas over the theory of integer arrays extended with free sort and function symbols.
  | QF_AX              -- ^ Quantifier-free formulas over the theory of arrays with extensionality.
  | QF_BV              -- ^ Quantifier-free formulas over the theory of fixed-size bitvectors.
  | QF_IDL             -- ^ Difference Logic over the integers. Boolean combinations of inequations of the form x - y < b where x and y are integer variables and b is an integer constant.
  | QF_LIA             -- ^ Unquantified linear integer arithmetic. In essence, Boolean combinations of inequations between linear polynomials over integer variables.
  | QF_LRA             -- ^ Unquantified linear real arithmetic. In essence, Boolean combinations of inequations between linear polynomials over real variables.
  | QF_NIA             -- ^ Quantifier-free integer arithmetic.
  | QF_NRA             -- ^ Quantifier-free real arithmetic.
  | QF_RDL             -- ^ Difference Logic over the reals. In essence, Boolean combinations of inequations of the form x - y < b where x and y are real variables and b is a rational constant.
  | QF_UF              -- ^ Unquantified formulas built over a signature of uninterpreted (i.e., free) sort and function symbols.
  | QF_UFBV            -- ^ Unquantified formulas over bitvectors with uninterpreted sort function and symbols.
  | QF_UFIDL           -- ^ Difference Logic over the integers (in essence) but with uninterpreted sort and function symbols.
  | QF_UFLIA           -- ^ Unquantified linear integer arithmetic with uninterpreted sort and function symbols.
  | QF_UFLRA           -- ^ Unquantified linear real arithmetic with uninterpreted sort and function symbols.
  | QF_UFNRA           -- ^ Unquantified non-linear real arithmetic with uninterpreted sort and function symbols.
  | QF_UFNIRA          -- ^ Unquantified non-linear real integer arithmetic with uninterpreted sort and function symbols.
  | UFLRA              -- ^ Linear real arithmetic with uninterpreted sort and function symbols.
  | UFNIA              -- ^ Non-linear integer arithmetic with uninterpreted sort and function symbols.
  | QF_FPBV            -- ^ Quantifier-free formulas over the theory of floating point numbers, arrays, and bit-vectors.
  | QF_FP              -- ^ Quantifier-free formulas over the theory of floating point numbers.
  | QF_FD              -- ^ Quantifier-free finite domains.
  | QF_S               -- ^ Quantifier-free formulas over the theory of strings.
  | Logic_ALL          -- ^ The catch-all value.
  | Logic_NONE         -- ^ Use this value when you want SBV to simply not set the logic.
  | CustomLogic String -- ^ In case you need a really custom string!
  deriving (Generic, NFData)

-- The show instance is "almost" the derived one, but not quite!
instance GShow Logic
instance Show Logic where
  show Logic_ALL       = "ALL"
  show (CustomLogic l) = l
  show l               = gshow l

{-# ANN type SMTInfoResponse ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN type Logic           ("HLint: ignore Use camelCase" :: String) #-}
