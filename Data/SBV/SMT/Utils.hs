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
        , annotateWithName
        , showTimeoutValue
        , alignDiagnostic
        , alignPlain
       )
       where

import Data.SBV.Core.Data

import Data.List (intercalate)
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

-- | Create an annotated term with the given name
annotateWithName :: String -> String -> String
annotateWithName nm x = "(! " ++ x ++ " :named |" ++ concatMap sanitize nm ++ "|)"
  where sanitize '|'  = "_bar_"
        sanitize '\\' = "_backslash_"
        sanitize c    = [c]

-- | Show a millisecond time-out value somewhat nicely
showTimeoutValue :: Int -> String
showTimeoutValue i = case (i `quotRem` 1000000, i `quotRem` 500000) of
                       ((s, 0), _)  -> shows s                              "s"
                       (_, (hs, 0)) -> shows (fromIntegral hs / (2::Float)) "s"
                       _            -> shows i "ms"

-- | Nicely align a potentially multi-line message with some tag, but prefix with three stars
alignDiagnostic :: String -> String -> String
alignDiagnostic = alignWithPrefix "*** "

-- | Nicely align a potentially multi-line message with some tag, no prefix.
alignPlain :: String -> String -> String
alignPlain = alignWithPrefix ""

-- | Align with some given prefix
alignWithPrefix :: String -> String -> String -> String
alignWithPrefix pre tag multi = intercalate "\n" $ zipWith (++) (tag : repeat (pre ++ replicate (length tag - length pre) ' ')) (filter (not . null) (lines multi))
