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

{-# LANGUAGE DeriveGeneric #-}

module Data.SBV.Control.Types (
       CheckSatResult(..)
     , Logic(..)
     , SMTOption(..)
     , SMTInfoFlag(..)
     , SMTErrorBehavior(..)
     , SMTReasonUnknown(..)
     , SMTInfoResponse(..)
     ) where

import Generics.Deriving.Base (Generic)
import Generics.Deriving.Show (GShow, gshow)

import Control.DeepSeq (NFData(..))

-- | Result of a 'checkSat' or 'checkSatAssuming' call.
data CheckSatResult = Sat | Unsat | Unk
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
                      | UnknownOther      String
                      deriving Show

-- | Collectable information from the solver.
data SMTInfoResponse = Resp_Unsupported
                     | Resp_AllStatistics        [(String, String)]
                     | Resp_AssertionStackLevels Integer
                     | Resp_Authors              [String]
                     | Resp_Error                SMTErrorBehavior
                     | Resp_Name                 String
                     | Resp_ReasonUnknown        SMTReasonUnknown
                     | Resp_Version              String
                     | Resp_InfoKeyword          String
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

-- | Option values that can be set in the solver. Note that not
-- all solvers may support all of these!
data SMTOption = DiagnosticOutputChannel FilePath
               | GlobalDeclarations      Bool
               -- | :interactive-mode b_value
               -- | :print-success b_value
               -- | :produce-assertions b_value
               -- | :produce-assignments b_value
               -- | :produce-models b_value
               | ProduceProofs           Bool
               | ProduceUnsatAssumptions Bool
               | ProduceUnsatCores       Bool
               | RandomSeed              Integer
               -- | :regular-output-channel string
               -- | :reproducible-resource-limit numeral
               -- | :verbosity numeral
               -- Strictly speaking, the following is not an option; but it fits well here.
               -- I think that's a wart in the SMTLib document itself.
               | SetLogic                Logic

instance NFData SMTOption where
  rnf (DiagnosticOutputChannel f) = rnf f `seq` ()
  rnf (GlobalDeclarations b)      = rnf b `seq` ()
  rnf (ProduceProofs b)           = rnf b `seq` ()
  rnf (ProduceUnsatAssumptions b) = rnf b `seq` ()
  rnf (ProduceUnsatCores b)       = rnf b `seq` ()
  rnf (RandomSeed i)              = rnf i `seq` ()
  rnf (SetLogic l)                = rnf l `seq` ()

-- SMTLib's True/False is spelled differently than Haskell's.
smtBool :: Bool -> String
smtBool True  = "true"
smtBool False = "false"

-- Show instance for SMTOption maintains smt-lib format per the SMTLib2 standard document.
instance Show SMTOption where
  show (DiagnosticOutputChannel f) = unwords [":diagnostic-output-channel", show f]
  show (GlobalDeclarations      b) = unwords [":global-declarations",       smtBool b]
  show (ProduceProofs           b) = unwords [":produce-proofs",            smtBool b]
  show (ProduceUnsatAssumptions b) = unwords [":produce-unsat-assumptions", smtBool b]
  show (ProduceUnsatCores       b) = unwords [":produce-unsat-cores",       smtBool b]
  show (RandomSeed              i) = unwords [":random-seed",               show i]
  show (SetLogic                i) = show i

-- | SMT-Lib logics. If left unspecified SBV will pick the logic based on what it determines is needed. However, the
-- user can override this choice using the tactic 'SetOptions' This is especially handy if one is experimenting with custom
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
  | QF_FD              -- ^ Quantifier-free finite domains
  | Logic_ALL          -- ^ The catch-all value
  | CustomLogic String -- ^ In case you need a really custom string!
  deriving Generic

-- The show instance is "almost" the derived one, but not quite!
instance GShow Logic
instance Show Logic where
  show Logic_ALL       = "ALL"
  show (CustomLogic l) = l
  show l               = gshow l

instance NFData Logic where
   rnf x = x `seq` ()

{-# ANN type SMTInfoResponse ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN type Logic           ("HLint: ignore Use camelCase" :: String) #-}
