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

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.SBV.Control.Query (
       send, ask
     , CheckSatResult(..), checkSat, checkSatAssuming, getUnsatCore, getProof, push, pop, getAssertionStackDepth, reset, exit
     , getValue, getModel
     , SMTOption(..)
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

import Data.List (unzip3, intercalate, nubBy)
import Data.Function (on)

import Data.SBV.Core.Data

import Data.SBV.Core.Symbolic (QueryState(..), Query(..), SMTResult(..), State(..))

import Data.SBV.SMT.Utils
import Data.SBV.Utils.SExpr

import Data.SBV.Control.Types
import Data.SBV.Control.Utils

import Data.IORef (readIORef)

import Generics.Deriving.Show

-- | An Assignment of a model binding
data Assignment = Assign SVal CW

-- | Ask solver for info.
getInfo :: SMTInfoFlag -> Query SMTInfoResponse
getInfo flag = do
    let cmd = "(get-info " ++ show flag ++ ")"
        bad = unexpected "getInfo" cmd "a valid get-info response" Nothing

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

-- | 'Query' as a 'SolverContext'.
instance SolverContext Query where
   constrain          = addQueryConstraint Nothing
   namedConstraint nm = addQueryConstraint (Just nm)

   setOption o
     | isStartModeOption o = error $ unlines [ ""
                                             , "*** Data.SBV: " ++ show (gshow o) ++ " can only be set at start-up time."
                                             , "*** Hint: Move the call to 'setOption' before the query."
                                             ]
     | True                = case o of
                               SetLogic l -> send $ "(set-logic "  ++ show l ++ ")"   -- This will actually never happen since SetLogic is start-mode. But for completion.
                               _          -> send $ "(set-option " ++ show o ++ ")"


-- | Adding a constraint, possibly named. Only used internally.
-- Use 'constrain' and 'namedConstraint' from user programs.
addQueryConstraint :: Maybe String -> SBool -> Query ()
addQueryConstraint mbNm b = do sw <- inNewContext (`sbvToSW` b)
                               send $ "(assert " ++ mkNamed mbNm (show sw)  ++ ")"
   where mkNamed Nothing   s = s
         mkNamed (Just nm) s = annotateWithName nm s

-- | Check for satisfiability.
checkSat :: Query CheckSatResult
checkSat = do let cmd = "(check-sat)"
                  bad = unexpected "checkSat" cmd "one of sat/unsat/unknown" Nothing
              r <- ask cmd
              parse r bad $ \case ECon "sat"     -> return Sat
                                  ECon "unsat"   -> return Unsat
                                  ECon "unknown" -> return Unk
                                  _              -> bad r Nothing

-- | Check for satisfiability, under the given conditions. Similar to 'checkSat'
-- except it allows making further assumptions as captured by the first argument
-- of booleans. If the result is 'Unsat', the user will also receive a subset of
-- the given assumptions that led to the 'Unsat' conclusion. Note that while this
-- set will be a subset of the inputs, it is not necessarily guaranteed to be minimal.
--
-- You must have arranged for the production of unsat-assumptions
-- first (/via/ @tactic $ SetOptions [ProduceUnsatAssumptions True]@)
-- for this call to not error out!
--
-- Usage note: 'getUnsatCore' is usually easier to use than 'checkSatAssuming', as it
-- allows the use of named assertions, as obtained by 'namedAssert'. If 'getUnsatCore'
-- fills your needs, you should definitely prefer it over 'checkSatAssuming'.
checkSatAssuming :: [SBool] -> Query (CheckSatResult, Maybe [SBool])
checkSatAssuming sBools = do
        -- sigh.. SMT-Lib requires the values to be literals only. So, create proxies.
        let mkAssumption st = do swsOriginal <- mapM (\sb -> sbvToSW st sb >>= \sw -> return (sw, sb)) sBools

                                 -- drop duplicates and trues
                                 let swbs = [p | p@(sw, _) <- nubBy ((==) `on` fst) swsOriginal, sw /= trueSW]

                                     translate (sw, sb) = (nm, decls, (proxy, sb))
                                        where nm    = show sw
                                              proxy = "__assumption_proxy_" ++ nm
                                              decls = [ "(declare-const " ++ proxy ++ " Bool)"
                                                      , "(assert (= " ++ proxy ++ " " ++ nm ++ "))"
                                                      ]

                                 return $ map translate swbs

        assumptions <- inNewContext mkAssumption

        let (origNames, declss, proxyMap) = unzip3 assumptions

        let cmd = "(check-sat-assuming (" ++ unwords (map fst proxyMap) ++ "))"
            bad = unexpected "checkSatAssuming" cmd "one of sat/unsat/unknown"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       tactic $ SetOptions [ProduceUnsatAssumptions True]"
                                  , ""
                                  , "to make sure the solver is ready for producing unsat assumptions."
                                  ]

        mapM_ send $ concat declss
        r <- ask cmd

        let grabUnsat = do as <- getUnsatAssumptions origNames proxyMap
                           return (Unsat, Just as)

        parse r bad $ \case ECon "sat"     -> return (Sat, Nothing)
                            ECon "unsat"   -> grabUnsat
                            ECon "unknown" -> return (Unk, Nothing)
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

-- | Reset the solver, bringing it to the state at the beginning. Note that this makes the
-- solver "forget" everything we have sent down, so subsequence interaction will have no
-- knowledge of the bindings to variables constructed so far. Use with care.
reset :: Query ()
reset = do send "(reset)"
           modify' $ \s -> s{queryAssertionStackDepth = 0}

-- | Exit the solver. This action will cause the solver to terminate. Needless to say,
-- trying to communicate with the solver after issuing "exit" will simply fail.
exit :: Query ()
exit = do send "(exit)"
          modify' $ \s -> s{queryAssertionStackDepth = 0}

-- | Retrieve the unsat-core. Note you must have arranged for
-- unsat cores to be produced first (/via/ @tactic $ SetOptions [ProduceUnsatCores True]@)
-- for this call to not error out!
getUnsatCore :: Query [String]
getUnsatCore = do
        let cmd = "(get-unsat-core)"
            bad = unexpected "getUnsatCore" cmd "an unsat-core response"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       tactic $ SetOptions [ProduceUnsatCores True]"
                                  , ""
                                  , "to make sure the solver is ready for producing unsat cores."
                                  ]


            fromECon (ECon s) = Just s
            fromECon _        = Nothing

            noBar = reverse . dropWhile bar . reverse . dropWhile bar
            bar   = (== '|')

        r <- ask cmd

        parse r bad $ \case
           EApp es | Just xs <- mapM fromECon es -> return $ map noBar xs
           _                                     -> bad r Nothing

-- | Retrieve the proof. Note you must have arranged for
-- unsat cores to be produced first (/via/ @tactic $ SetOptions [ProduceProofs True]@)
-- for this call to not error out!
--
-- A proof is simply a 'String', as returned by the solver. We return an 'Either' type,
-- with the 'Left' choice if something goes wrong with an explanation. In the future, SBV might
-- provide a better datatype, depending on the use cases. Please get in touch if you
-- use this function and can suggest a better API.
getProof :: Query String
getProof = do
        let cmd = "(get-proof)"
            bad = unexpected "getProof" cmd "a get-proof response"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       tactic $ SetOptions [ProduceProofs True]"
                                  , ""
                                  , "to make sure the solver is ready for producing proofs."
                                  ]


        r <- ask cmd

        -- we only care about the fact that we can parse the output, so the
        -- result of parsing is ignored.
        parse r bad $ \_ -> return r

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
