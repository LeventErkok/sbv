-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.Utils
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- A few internally used types/routines
-----------------------------------------------------------------------------

module Data.SBV.SMT.Utils (
          SMTLibConverter
        , SMTLibIncConverter
       )
       where

import Data.SBV.Core.Data

import qualified Data.Set as Set (Set)

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibConverter a =  Set.Set Kind                 -- ^ Kinds used in the problem
                       -> Bool                         -- ^ is this a sat problem?
                       -> [String]                     -- ^ extra comments to place on top
                       -> [(Quantifier, NamedSymVar)]  -- ^ inputs and aliasing names
                       -> [Either SW (SW, [SW])]       -- ^ skolemized inputs
                       -> [(SW, CW)]                   -- ^ constants
                       -> [((Int, Kind, Kind), [SW])]  -- ^ auto-generated tables
                       -> [(Int, ArrayInfo)]           -- ^ user specified arrays
                       -> [(String, SBVType)]          -- ^ uninterpreted functions/constants
                       -> [(String, [String])]         -- ^ user given axioms
                       -> SBVPgm                       -- ^ assignments
                       -> [(Maybe String, SW)]         -- ^ extra constraints
                       -> SW                           -- ^ output variable
                       -> SMTConfig                    -- ^ configuration
                       -> CaseCond                     -- ^ case analysis
                       -> a

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibIncConverter a =  [(SW, CW)]    -- ^ constants
                          -> SBVPgm        -- ^ assignments
                          -> SMTConfig     -- ^ configuration
                          -> a
