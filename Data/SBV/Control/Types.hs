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

module Data.SBV.Control.Types (
       CheckSatResult(..)
     , SMTOption(..)
     , Assignment(..)
     , SMTInfoFlag(..)
     , SMTErrorBehavior(..)
     , SMTReasonUnknown(..)
     , SMTInfoResponse(..)
     ) where

import Data.SBV.Core.Data (SVal, CW)

-- | An Assignment of a model binding
data Assignment = Assign SVal CW

-- | Result of a 'checkSat' call.
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
                      | UnknownOther String
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

-- | Show instance for SMTInfoFlag maintains smt-lib format per the SMTLib2 standard document.
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
               | RandomSeed Integer

-- | Show instance for SMTOption maintains smt-lib format per the SMTLib2 standard document.
instance Show SMTOption where
  show (DiagnosticOutputChannel f) = ":diagnostic-output-channel " ++ show f
  show (RandomSeed              i) = ":random-seed " ++ show i

{-# ANN type SMTInfoResponse ("HLint: ignore Use camelCase" :: String) #-}
