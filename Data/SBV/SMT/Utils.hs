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

{-# LANGUAGE NamedFieldPuns #-}

module Data.SBV.SMT.Utils (
          SMTLibConverter
        , SMTLibIncConverter
        , annotateWithName
        , showTimeoutValue
        , alignDiagnostic
        , alignPlain
        , debug
        , mergeSExpr
        , SMTException(..)
        , stringToQFS
        , qfsToString
       )
       where

import qualified Control.Exception as C

import Data.SBV.Core.Data
import Data.SBV.Utils.Lib (joinArgs)

import Data.Char (chr, ord)

import Data.List (intercalate)
import qualified Data.Set as Set (Set)

import System.Exit (ExitCode(..))

import Numeric (readHex, readOct, showHex)

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibConverter a =  Set.Set Kind                                  -- ^ Kinds used in the problem
                       -> Bool                                          -- ^ is this a sat problem?
                       -> [String]                                      -- ^ extra comments to place on top
                       -> ([(Quantifier, NamedSymVar)], [NamedSymVar])  -- ^ inputs and aliasing names and trackers
                       -> [Either SW (SW, [SW])]                        -- ^ skolemized inputs
                       -> [(SW, CW)]                                    -- ^ constants
                       -> [((Int, Kind, Kind), [SW])]                   -- ^ auto-generated tables
                       -> [(Int, ArrayInfo)]                            -- ^ user specified arrays
                       -> [(String, SBVType)]                           -- ^ uninterpreted functions/constants
                       -> [(String, [String])]                          -- ^ user given axioms
                       -> SBVPgm                                        -- ^ assignments
                       -> [(Maybe String, SW)]                          -- ^ extra constraints
                       -> SW                                            -- ^ output variable
                       -> SMTConfig                                     -- ^ configuration
                       -> a

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibIncConverter a =  [NamedSymVar]               -- ^ inputs
                          -> Set.Set Kind                -- ^ Newly registered kinds
                          -> [(SW, CW)]                  -- ^ constants
                          -> [(Int, ArrayInfo)]          -- ^ newly created arrays
                          -> [((Int, Kind, Kind), [SW])] -- ^ newly created tables
                          -> SBVPgm                      -- ^ assignments
                          -> SMTConfig                   -- ^ configuration
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

       skipString ('\\':'"' :cs) = skipString cs
       skipString ('\\':'\\':cs) = skipString cs
       skipString ('"':'"':cs)   = skipString cs
       skipString ('"':cs)       = cs
       skipString (_:cs)         = skipString cs
       skipString []             = []             -- Oh dear, line finished, but the string didn't. We're in trouble. Ignore!

       skipBar ('|':cs) = cs
       skipBar (_:cs)   = skipBar cs
       skipBar []       = []                     -- Oh dear, line finished, but the string didn't. We're in trouble. Ignore!

-- | An SMT exception generated by the back-end solver and is thrown from SBV. If the solver
-- ever responds with a non-success value for a command, SBV will throw an 'SMTException',
-- it so the user can process it as required. The provided 'Show' instance will render the failure
-- nicely. Note that if you ever catch this exception, the solver is no longer alive: You should either
-- throw the exception up, or do other proper clean-up before continuing.
data SMTException = SMTException {
                          smtExceptionDescription :: String
                        , smtExceptionSent        :: String
                        , smtExceptionExpected    :: String
                        , smtExceptionReceived    :: String
                        , smtExceptionStdOut      :: String
                        , smtExceptionStdErr      :: Maybe String
                        , smtExceptionExitCode    :: Maybe ExitCode
                        , smtExceptionConfig      :: SMTConfig
                        , smtExceptionReason      :: Maybe [String]
                        , smtExceptionHint        :: Maybe [String]
                        }

-- | SMTExceptions are throwable. A simple "show" will render this exception nicely
-- though of course you can inspect the individual fields as necessary.
instance C.Exception SMTException

-- | A fairly nice rendering of the exception, for display purposes.
instance Show SMTException where
 show SMTException { smtExceptionDescription
                   , smtExceptionSent
                   , smtExceptionExpected
                   , smtExceptionReceived
                   , smtExceptionStdOut
                   , smtExceptionStdErr
                   , smtExceptionExitCode
                   , smtExceptionConfig
                   , smtExceptionReason
                   , smtExceptionHint
                   }

         = let grp1 = [ ""
                      , "*** " ++ smtExceptionDescription ++ ":"
                      , "***"
                      , "***    Sent      : " `alignDiagnostic` smtExceptionSent
                      , "***    Expected  : " `alignDiagnostic` smtExceptionExpected
                      , "***    Received  : " `alignDiagnostic` smtExceptionReceived
                      ]

               grp2 =  ["***    Stdout    : " `alignDiagnostic` smtExceptionStdOut | not $ null smtExceptionStdOut                    ]
                    ++ ["***    Stderr    : " `alignDiagnostic` err                | Just err  <- [smtExceptionStdErr], not $ null err]
                    ++ ["***    Exit code : " `alignDiagnostic` show ec            | Just ec   <- [smtExceptionExitCode]              ]
                    ++ ["***    Executable: " `alignDiagnostic` executable (solver smtExceptionConfig)                                ]
                    ++ ["***    Options   : " `alignDiagnostic` joinArgs (options (solver smtExceptionConfig) smtExceptionConfig)     ]

               grp3 =  ["***    Reason    : " `alignDiagnostic` unlines rsn | Just rsn <- [smtExceptionReason]]
                    ++ ["***    Hint      : " `alignDiagnostic` unlines hnt | Just hnt <- [smtExceptionHint  ]]

               sep1
                | null grp2 = []
                | True      = ["***"]

               sep2
                 | null grp3 = []
                 | True      = ["***"]

          in unlines $ grp1 ++ sep1 ++ grp2 ++ sep2 ++ grp3

-- | Given a QF_S string (i.e., one that works in the string theory), convert it to a Haskell equivalent
qfsToString :: String -> String
qfsToString = go
  where go ""                                                              = ""
        go ('\\':'n'       : rest)                                         = chr 10 : go rest
        go ('\\':'v'       : rest)                                         = chr 11 : go rest
        go ('\\':'f'       : rest)                                         = chr 12 : go rest
        go ('\\':'r'       : rest)                                         = chr 13 : go rest
        go ('\\':'x':c1:c2 : rest) | [(v, "")] <- readHex [c1, c2]         = chr  v : go rest
        go ('\\':c1:c2:c3  : rest) | [(v, "")] <- readOct [c1, c2, c3]     = chr  v : go rest
        go ('\\':'\\'      : rest)                                         = '\\'   : go rest
        go (c              : rest)                                         = c      : go rest

-- | Given a Haskell, convert it to one that's understood by the QF_S logic
stringToQFS :: String -> String
stringToQFS s = '\"' : concatMap cvt s ++ "\""
  where -- strings are almost just show, but escapes are different. Sigh
        cvt c
         | 0 <= o && o < 32
         = escapeTable !! o
         | c == '\\'
         = "\\\\"
         | c == '"'
         = "\"\""
         | o >= 128 && o < 256
         = "\\x" ++ showHex (ord c) ""
         | o > 256
         = error $ "Data.SBV: stringToQFS: Haskell character: " ++ show c ++ " is not representable in QF_S"
         | True
         = [c]
         where o = ord c

        -- | First 32 values are coded in a custom way by Z3:
        escapeTable :: [String]
        escapeTable = [ "\\x00", "\\x01", "\\x02", "\\x03", "\\x04", "\\x05", "\\x06", "\\x07", "\\x08", "\\x09", "\\n",   "\\v",   "\\f",   "\\r",   "\\x0E", "\\x0F"
                      , "\\x10", "\\x11", "\\x12", "\\x13", "\\x14", "\\x15", "\\x16", "\\x17", "\\x18", "\\x19", "\\x1A", "\\x1B", "\\x1C", "\\x1D", "\\x1E", "\\x1F"
                      ]
