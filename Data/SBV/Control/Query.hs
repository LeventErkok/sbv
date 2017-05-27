-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control.Query
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Querying a solver interactively.
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}

module Data.SBV.Control.Query (
       assert
     , send, ask
     , CheckSatResult(..), checkSat, push, pop, getAssertionStackDepth, reset
     , getValue, getModel
     , SMTOption(..), setOption
     , SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..), getInfo
     , Logic(..), Assignment(..)
     , ignoreExitCode
     , (|->)
     , result
     , success
     , failure
     , sbvResume
     , io
     ) where

import Control.Monad            (unless)
import Control.Monad.State.Lazy (get, modify')

import Data.List (intercalate)

import Data.SBV.Core.Data

import Data.SBV.Core.Symbolic (QueryState(..), Query(..), SMTResult(..), State(..))

import Data.SBV.Utils.SExpr

import Data.SBV.Control.Types
import Data.SBV.Control.Utils

import Data.IORef (readIORef)

-- | An Assignment of a model binding
data Assignment = Assign SVal CW

-- | Set an option. Note that "SetLogic" is custom, as it is really not
-- an option. Note that sending this yourself is risky, as when this
-- call is done, you already have a logic set. The solver might reject it.
setOption :: SMTOption -> Query ()
setOption (SetLogic l) = send $ "(set-logic "  ++ show l ++ ")"
setOption o            = send $ "(set-option " ++ show o ++ ")"

-- | Ask solver for info.
getInfo :: SMTInfoFlag -> Query SMTInfoResponse
getInfo flag = do
    let cmd = "(get-info " ++ show flag ++ ")"
        bad = unexpected "getInfo" cmd "a valid get-info response"

        isAllStatistics AllStatistics = True
        isAllStatistics _             = False

        isAllStat = isAllStatistics flag

        -- remove unnecessary quoting
        unquote ('"':s@(_:_)) | last s == '"' = init s
        unquote s                             = s

        -- sort of a light-hearted show
        serialize (ECon s)      = unquote s
        serialize (ENum (i, _)) = show i
        serialize (EReal   r)   = show r
        serialize (EFloat  f)   = show f
        serialize (EDouble d)   = show d
        serialize (EApp [x])    = serialize x
        serialize (EApp ss)     = "(" ++ unwords (map serialize ss) ++ ")"

        grabAllStat k v = (serialize k, serialize v)

        -- we're trying to do our best to get key-value pairs here, but this
        -- is necessarily a half-hearted attempt.
        grabAllStats (EApp xs) = walk xs
           where walk []             = []
                 walk [t]            = [grabAllStat t (ECon "")]
                 walk (t : v : rest) =  grabAllStat t v          : walk rest
        grabAllStats o = [grabAllStat o (ECon "")]

    r <- ask cmd

    parse r bad $ \pe ->
       if isAllStat
          then return $ Resp_AllStatistics $ grabAllStats pe
          else case pe of
                 ECon "unsupported"                                        -> return Resp_Unsupported
                 EApp [ECon ":assertion-stack-levels", ENum (i, _)]        -> return $ Resp_AssertionStackLevels i
                 EApp (ECon ":authors" : ns)                               -> return $ Resp_Authors (map serialize ns)
                 EApp [ECon ":error-behavior", ECon "immediate-exit"]      -> return $ Resp_Error ErrorImmediateExit
                 EApp [ECon ":error-behavior", ECon "continued-execution"] -> return $ Resp_Error ErrorContinuedExecution
                 EApp (ECon ":name" : o)                                   -> return $ Resp_Name (serialize (EApp o))
                 EApp [ECon ":reason-unknown", ECon "memout"]              -> return $ Resp_ReasonUnknown UnknownMemOut
                 EApp [ECon ":reason-unknown", ECon "incomplete"]          -> return $ Resp_ReasonUnknown UnknownIncomplete
                 EApp (ECon ":reason-unknown" : o)                         -> return $ Resp_ReasonUnknown (UnknownOther (serialize (EApp o)))
                 EApp (ECon ":version" : o)                                -> return $ Resp_Version (serialize (EApp o))
                 _                                                         -> return $ Resp_InfoKeyword (serialize pe)

-- | Assert a new constraint.
assert :: SBool -> Query ()
assert s = do sw <- inNewContext (`sbvToSW` s)
              send $ "(assert " ++ show sw ++ ")"

-- | Check for satisfiability.
checkSat :: Query CheckSatResult
checkSat = do let cmd = "(check-sat)"
                  bad = unexpected "checkSat" cmd "one of sat/unsat/unknown"
              r <- ask cmd
              parse r bad $ \case ECon "sat"     -> return Sat
                                  ECon "unsat"   -> return Unsat
                                  ECon "unknown" -> return Unk
                                  _              -> bad r Nothing

-- | The current assertion stack depth, i.e., #push - #pops after start. Always non-negative.
getAssertionStackDepth :: Query Int
getAssertionStackDepth = queryAssertionStackDepth <$>  get

-- | Push the context, entering a new one. Pushes multiple levels if /n/ > 1.
push :: Int -> Query ()
push i
 | i <= 0 = error $ "Data.SBV: push requires a strictly positive level argument, received: " ++ show i
 | True   = do depth <- getAssertionStackDepth
               send $ "(push " ++ show i ++ ")"
               modify' $ \s -> s{queryAssertionStackDepth = depth + i}

-- | Pop the context, exiting a new one. Pops multiple levels if /n/ > 1. It's an error to pop levels that don't exist.
pop :: Int -> Query ()
pop i
 | i <= 0 = error $ "Data.SBV: pop requires a strictly positive level argument, received: " ++ show i
 | True   = do depth <- getAssertionStackDepth
               if i > depth
                  then error $ "Data.SBV: Illegally trying to pop " ++ shl i ++ ", at current level: " ++ show depth
                  else do send $ "(pop " ++ show i ++ ")"
                          modify' $ \s -> s{queryAssertionStackDepth = depth - i}
   where shl 1 = "one level"
         shl n = show n ++ " levels"

-- | Reset the solver, bringing it to the state at the beginning
reset :: Query ()
reset = do send "(reset)"
           modify' $ \s -> s{queryAssertionStackDepth = 0}

-- | Make an assignment. The type 'Assignment' is abstract, see 'success' for an example use case.
infix 1 |->
(|->) :: SymWord a => SBV a -> a -> Assignment
SBV a |-> v = case literal v of
                SBV (SVal _ (Left cw)) -> Assign a cw
                r                      -> error $ "Data.SBV: Impossible happened in |->: Cannot construct a CW with literal: " ++ show r

-- | Produce the query result from an assignment.
success :: [Assignment] -> Query [SMTResult]
success asgns = do QueryState{queryConfig} <- get

                   let grabValues st = do let extract (Assign s n) = sbvToSW st (SBV s) >>= \sw -> return (sw, n)

                                          modelAssignment <- mapM extract asgns

                                          inps <- reverse <$> readIORef (rinps st)

                                          -- sanity checks
                                          --     - All existentials should be given a value
                                          --     - No duplicates
                                          --     - No bindings to vars that are not inputs
                                          let userSS = map fst modelAssignment

                                              missing, extra, dup :: [String]
                                              missing = [n | (EX, (s, n)) <- inps, s `notElem` userSS]
                                              extra   = [show s | s <- userSS, s `notElem` map (fst . snd) inps]
                                              dup     = let walk []     = []
                                                            walk (n:ns)
                                                              | n `elem` ns = show n : walk (filter (/= n) ns)
                                                              | True        = walk ns
                                                        in walk userSS

                                          unless (null (missing ++ extra ++ dup)) $ do

                                                let misTag = "***   Missing inputs"
                                                    dupTag = "***   Duplicate bindings"
                                                    extTag = "***   Extra bindings"

                                                    maxLen = maximum $  0
                                                                      : [length misTag | not (null missing)]
                                                                     ++ [length extTag | not (null extra)]
                                                                     ++ [length dupTag | not (null dup)]

                                                    align s = s ++ replicate (maxLen - length s) ' ' ++ ": "

                                                error $ unlines $ [""
                                                                  , "*** Data.SBV: Query model construction has a faulty assignment."
                                                                  ]
                                                               ++ [ align misTag ++ intercalate ", "  missing | not (null missing)]
                                                               ++ [ align extTag ++ intercalate ", "  extra   | not (null extra)  ]
                                                               ++ [ align dupTag ++ intercalate ", "  dup     | not (null dup)    ]
                                                               ++ [ "*** Data.SBV: Check your query result construction!" ]

                                          return modelAssignment

                   assocs <- inNewContext grabValues

                   let m = SMTModel { modelObjectives = []
                                    , modelAssocs     = [(show s, c) | (s, c) <- assocs]
                                    }

                   result $ Satisfiable queryConfig m

-- | Produce this answer as the result.
result :: SMTResult -> Query [SMTResult]
result x = return [x]

-- | Fail with error.
failure :: [String] -> Query [SMTResult]
failure ms = do QueryState{queryConfig} <- get
                result $ ProofError queryConfig ms

-- | Run what SBV would've run, should we not have taken control. Note that
-- if you call this function, SBV will issue a call to check-sat and then
-- collect the model with respect to all the changes the query has performed.
-- If you already do have a model built during the query, use 'result' to
-- return it, instead of telling sbv to do it on its own.
sbvResume :: Query [SMTResult]
sbvResume = do QueryState{queryDefault, queryIgnoreExitCode} <- get
               io $ queryDefault queryIgnoreExitCode
