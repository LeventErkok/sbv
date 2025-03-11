-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.SMT.Utils
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A few internally used types/routines
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SMT.Utils (
          SMTLibConverter
        , SMTLibIncConverter
        , witnessName
        , addAnnotations
        , showTimeoutValue
        , alignDiagnostic
        , alignPlain
        , debug
        , mergeSExpr
        , SBVException(..)
        , startTranscript
        , finalizeTranscript
        , recordTranscript
        , recordException
        , recordEndTime
        , TranscriptMsg(..)
       )
       where

import qualified Control.Exception as C

import Control.Monad (zipWithM_)
import Control.Monad.Trans (MonadIO, liftIO)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (QueryContext, CnstMap, SMTDef, ResultInp(..), ProgInfo(..), startTime)

import Data.SBV.Utils.Lib   (joinArgs)
import Data.SBV.Utils.TDiff (Timing(..), showTDiff)

import Data.IORef (writeIORef)
import Data.Time  (getZonedTime, defaultTimeLocale, formatTime, diffUTCTime, getCurrentTime)

import Data.Char  (isSpace)
import Data.Maybe (fromMaybe)
import Data.List  (intercalate)

import qualified Data.Set      as Set (Set)
import qualified Data.Sequence as S   (Seq)

import System.Directory (findExecutable)
import System.Exit      (ExitCode(..))

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibConverter a =  QueryContext                                   -- ^ Internal or external query?
                       -> ProgInfo                                       -- ^ Various program info
                       -> Set.Set Kind                                   -- ^ Kinds used in the problem
                       -> Bool                                           -- ^ is this a sat problem?
                       -> [String]                                       -- ^ extra comments to place on top
                       -> ResultInp                                      -- ^ inputs or params
                       -> (CnstMap, [(SV, CV)])                          -- ^ constants. The map, and as rendered in order
                       -> [((Int, Kind, Kind), [SV])]                    -- ^ auto-generated tables
                       -> [(String, (Bool, Maybe [String], SBVType))]    -- ^ uninterpreted functions/constants
                       -> [(SMTDef, SBVType)]                            -- ^ user given axioms/definitions
                       -> SBVPgm                                         -- ^ assignments
                       -> S.Seq (Bool, [(String, String)], SV)           -- ^ extra constraints
                       -> SV                                             -- ^ output variable
                       -> SMTConfig                                      -- ^ configuration
                       -> a

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibIncConverter a =  ProgInfo                                    -- ^ Various prog info
                          -> [NamedSymVar]                               -- ^ inputs
                          -> Set.Set Kind                                -- ^ new kinds
                          -> (CnstMap, [(SV, CV)])                       -- ^ all constants sofar, and new constants
                          -> [((Int, Kind, Kind), [SV])]                 -- ^ newly created tables
                          -> [(String, (Bool, Maybe [String], SBVType))] -- ^ newly created uninterpreted functions/constants
                          -> SBVPgm                                      -- ^ assignments
                          -> S.Seq (Bool, [(String, String)], SV)        -- ^ extra constraints
                          -> SMTConfig                                   -- ^ configuration
                          -> a

-- | The name of a witness for a type. We should make sure this doesn't conflict any reserved names, but I think the chances of that is
-- pretty low anyhow.
witnessName :: String -> String
witnessName = (++ "_witness")

-- | Create an annotated term
addAnnotations :: [(String, String)] -> String -> String
addAnnotations []   x = x
addAnnotations atts x = "(! " ++ x ++ " " ++ unwords (map mkAttr atts) ++ ")"
  where mkAttr (a, v) = a ++ " |" ++ concatMap sanitize v ++ "|"
        sanitize '|'  = "_bar_"
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
debug :: MonadIO m => SMTConfig -> [String] -> m ()
debug cfg
  | not (verbose cfg)             = const (return ())
  | Just f <- redirectVerbose cfg = liftIO . mapM_ (appendFile f . (++ "\n"))
  | True                          = liftIO . mapM_ putStrLn

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
               go i (';':cs) = go i (drop 1 (dropWhile (/= '\n') cs))
               go i (_  :cs) = go i cs

       grab i ls
         | i <= 0    = ([], ls)
       grab _ []     = ([], [])
       grab i (l:ls) = let (a, b) = grab (i+parenDiff l) ls in (l:a, b)

       skipString ('"':'"':cs)   = skipString cs
       skipString ('"':cs)       = cs
       skipString (_:cs)         = skipString cs
       skipString []             = []             -- Oh dear, line finished, but the string didn't. We're in trouble. Ignore!

       skipBar ('|':cs) = cs
       skipBar (_:cs)   = skipBar cs
       skipBar []       = []                     -- Oh dear, line finished, but the string didn't. We're in trouble. Ignore!

-- | An exception thrown from SBV. If the solver ever responds with a non-success value for a command,
-- SBV will throw an t'SBVException', it so the user can process it as required. The provided 'Show' instance
-- will render the failure nicely. Note that if you ever catch this exception, the solver is no longer alive:
-- You should either -- throw the exception up, or do other proper clean-up before continuing.
data SBVException = SBVException {
                          sbvExceptionDescription :: String
                        , sbvExceptionSent        :: Maybe String
                        , sbvExceptionExpected    :: Maybe String
                        , sbvExceptionReceived    :: Maybe String
                        , sbvExceptionStdOut      :: Maybe String
                        , sbvExceptionStdErr      :: Maybe String
                        , sbvExceptionExitCode    :: Maybe ExitCode
                        , sbvExceptionConfig      :: SMTConfig
                        , sbvExceptionReason      :: Maybe [String]
                        , sbvExceptionHint        :: Maybe [String]
                        }

-- | SBVExceptions are throwable. A simple "show" will render this exception nicely
-- though of course you can inspect the individual fields as necessary.
instance C.Exception SBVException

-- | A fairly nice rendering of the exception, for display purposes.
instance Show SBVException where
 show SBVException { sbvExceptionDescription
                   , sbvExceptionSent
                   , sbvExceptionExpected
                   , sbvExceptionReceived
                   , sbvExceptionStdOut
                   , sbvExceptionStdErr
                   , sbvExceptionExitCode
                   , sbvExceptionConfig
                   , sbvExceptionReason
                   , sbvExceptionHint
                   }

         = let grp1 = [ ""
                      , "*** Data.SBV: " ++ sbvExceptionDescription ++ ":"
                      ]

               grp2 =  ["***    Sent      : " `alignDiagnostic` snt     | Just snt  <- [sbvExceptionSent],     not $ null snt ]
                    ++ ["***    Expected  : " `alignDiagnostic` excp    | Just excp <- [sbvExceptionExpected], not $ null excp]
                    ++ ["***    Received  : " `alignDiagnostic` rcvd    | Just rcvd <- [sbvExceptionReceived], not $ null rcvd]

               grp3 =  ["***    Stdout    : " `alignDiagnostic` out     | Just out  <- [sbvExceptionStdOut],   not $ null out ]
                    ++ ["***    Stderr    : " `alignDiagnostic` err     | Just err  <- [sbvExceptionStdErr],   not $ null err ]
                    ++ ["***    Exit code : " `alignDiagnostic` show ec | Just ec   <- [sbvExceptionExitCode]                 ]
                    ++ ["***    Executable: " `alignDiagnostic` executable (solver sbvExceptionConfig)                                   ]
                    ++ ["***    Options   : " `alignDiagnostic` joinArgs (options (solver sbvExceptionConfig) sbvExceptionConfig)        ]

               grp4 =  ["***    Reason    : " `alignDiagnostic` unlines rsn | Just rsn <- [sbvExceptionReason]]
                    ++ ["***    Hint      : " `alignDiagnostic` unlines hnt | Just hnt <- [sbvExceptionHint  ]]

               join []     = []
               join [x]    = x
               join (g:gs) = case join gs of
                               []    -> g
                               rest  -> g ++ ["***"] ++ rest

          in unlines $ join [grp1, grp2, grp3, grp4]

-- | Compute and report the end time
recordEndTime :: SMTConfig -> State -> IO ()
recordEndTime SMTConfig{timing} state = case timing of
                                           NoTiming        -> return ()
                                           PrintTiming     -> do e <- elapsed
                                                                 putStrLn $ "*** SBV: Elapsed time: " ++ showTDiff e
                                           SaveTiming here -> writeIORef here =<< elapsed
  where elapsed = getCurrentTime >>= \end -> return $ diffUTCTime end (startTime state)

-- | Start a transcript file, if requested.
startTranscript :: Maybe FilePath -> SMTConfig -> IO ()
startTranscript Nothing  _   = return ()
startTranscript (Just f) cfg = do ts <- show <$> getZonedTime
                                  mbExecPath <- findExecutable (executable (solver cfg))
                                  writeFile f $ start ts mbExecPath
  where SMTSolver{name, options} = solver cfg
        start ts mbPath = unlines [ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                                  , ";;; SBV: Starting at " ++ ts
                                  , ";;;"
                                  , ";;;           Solver    : " ++ show name
                                  , ";;;           Executable: " ++ fromMaybe "Unable to locate the executable" mbPath
                                  , ";;;           Options   : " ++ unwords (options cfg ++ extraArgs cfg)
                                  , ";;;"
                                  , ";;; This file is an auto-generated loadable SMT-Lib file."
                                  , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                                  , ""
                                  ]

-- | Finish up the transcript file.
finalizeTranscript :: Maybe FilePath -> ExitCode -> IO ()
finalizeTranscript Nothing  _  = return ()
finalizeTranscript (Just f) ec = do ts <- show <$> getZonedTime
                                    appendFile f $ end ts
  where end ts = unlines [ ""
                         , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                         , ";;;"
                         , ";;; SBV: Finished at " ++ ts
                         , ";;;"
                         , ";;; Exit code: " ++ show ec
                         , ";;;"
                         , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                         ]

-- Kind of things we can record
data TranscriptMsg = SentMsg  String (Maybe Int) -- ^ Message sent, and time-out if any
                   | RecvMsg  String             -- ^ Message received
                   | DebugMsg String             -- ^ A debug message; neither sent nor received

-- If requested, record in the transcript file
recordTranscript :: Maybe FilePath -> TranscriptMsg -> IO ()
recordTranscript Nothing  _ = return ()
recordTranscript (Just f) m = do tsPre <- formatTime defaultTimeLocale "; [%T%Q" <$> getZonedTime
                                 let ts = take 15 $ tsPre ++ repeat '0'
                                 case m of
                                   SentMsg sent mbTimeOut  -> appendFile f $ unlines $ (ts ++ "] " ++ to mbTimeOut ++ "Sending:") : lines sent
                                   RecvMsg recv            -> appendFile f $ unlines $ case lines (dropWhile isSpace recv) of
                                                                                        []  -> [ts ++ "] Received: <NO RESPONSE>"]  -- can't really happen.
                                                                                        [x] -> [ts ++ "] Received: " ++ x]
                                                                                        xs  -> (ts ++ "] Received: ") : map (";   " ++) xs
                                   DebugMsg msg            -> let tag = ts ++ "] "
                                                                  emp = ';' : drop 1 (map (const ' ') tag)
                                                              in zipWithM_ (\t l -> appendFile f (t ++ l ++ "\n")) (tag : repeat emp) (lines msg)
        where to Nothing  = ""
              to (Just i) = "[Timeout: " ++ showTimeoutValue i ++ "] "
{-# INLINE recordTranscript #-}

-- Record the exception
recordException :: Maybe FilePath -> String -> IO ()
recordException Nothing  _ = return ()
recordException (Just f) m = do ts <- show <$> getZonedTime
                                appendFile f $ exc ts
  where exc ts = unlines $ [ ""
                           , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                           , ";;;"
                           , ";;; SBV: Caught an exception at " ++ ts
                           , ";;;"
                           ]
                        ++ [ ";;;   " ++ l | l <- dropWhile null (lines m) ]
                        ++ [ ";;;"
                           , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                           ]
