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
        , debug
        , mergeSExpr
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
                       -> a

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibIncConverter a =  [NamedSymVar] -- ^ inputs
                          -> Set.Set Kind  -- ^ Newly registered kinds
                          -> [(SW, CW)]    -- ^ constants
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

-- | Diagnostic message when verbose
debug :: SMTConfig -> [String] -> IO ()
debug cfg
  | not (verbose cfg)             = const (return ())
  | Just f <- redirectVerbose cfg = mapM_ (appendFile f . (++ "\n"))
  | True                          = mapM_ putStrLn

-- | In case the SMT-Lib solver returns a response over multiple lines, compress them so we have
-- each S-Expression spanning only a single line.
mergeSExpr :: [String] -> [String]
mergeSExpr []       = []
mergeSExpr (x:xs)
 | d == 0 = x : mergeSExpr xs
 | True   = let (f, r) = grab d xs in unlines (x:f) : mergeSExpr r
 where d = parenDiff x

       parenDiff :: String -> Int
       parenDiff = go 0
         where go i ""       = i
               go i ('(':cs) = let i'= i+1 in i' `seq` go i' cs
               go i (')':cs) = let i'= i-1 in i' `seq` go i' cs
               go i ('"':cs) = go i (skipString cs)
               go i ('|':cs) = go i (skipBar cs)
               go i (_  :cs) = go i cs

       grab i ls
         | i <= 0    = ([], ls)
       grab _ []     = ([], [])
       grab i (l:ls) = let (a, b) = grab (i+parenDiff l) ls in (l:a, b)

       skipString ('\\':'"':cs) = skipString cs
       skipString ('"':'"':cs)  = skipString cs
       skipString ('"':cs)      = cs
       skipString (_:cs)        = skipString cs
       skipString []            = []             -- Oh dear, line finished, but the string didn't. We're in trouble. Ignore!

       skipBar ('|':cs) = cs
       skipBar (_:cs)   = skipBar cs
       skipBar []       = []                     -- Oh dear, line finished, but the string didn't. We're in trouble. Ignore!

