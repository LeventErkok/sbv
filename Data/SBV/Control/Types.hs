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
     ) where

-- | Result of a 'checkSat' call.
data CheckSatResult = Sat | Unsat | Unk
                    deriving (Eq, Show)

-- | Option values that can be set in the solver. Note that not
-- all solvers may support all of these!
data SMTOption = DiagnosticOutputChannel FilePath

-- | Show instance for SMTOption maintains smt-lib format per the
-- SMTLib2 standard document
instance Show SMTOption where
   show (DiagnosticOutputChannel f) = ":diagnostic-output-channel " ++ show f
