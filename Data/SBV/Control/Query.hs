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
{-# LANGUAGE TupleSections  #-}
{-# LANGUAGE Rank2Types     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.SBV.Control.Query (
       send, ask, retrieveResponse
     , CheckSatResult(..), checkSat, checkSatUsing, checkSatAssuming, checkSatAssumingWithUnsatisfiableSet
     , getUnsatCore, getProof, getInterpolant, getAssignment, getOption, freshVar, freshVar_, push, pop, getAssertionStackDepth
     , inNewAssertionStack, echo, caseSplit, resetAssertions, exit, getAssertions, getValue, getUninterpretedValue, getModel, getSMTResult
     , getLexicographicOptResults, getIndependentOptResults, getParetoOptResults, getAllSatResult, getUnknownReason
     , SMTOption(..), SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..), getInfo
     , Logic(..), Assignment(..)
     , ignoreExitCode, timeout
     , (|->)
     , mkSMTResult
     , io
     ) where

import Control.Monad            (unless, when, zipWithM)
import Control.Monad.State.Lazy (get)

import Data.IORef (readIORef)

import qualified Data.Map    as M
import qualified Data.IntMap as IM

import Data.Char     (toLower)
import Data.List     (unzip3, intercalate, nubBy, sortBy)
import Data.Maybe    (listToMaybe, catMaybes)
import Data.Function (on)

import Data.SBV.Core.Data

import Data.SBV.Core.Symbolic   (QueryState(..), Query(..), SMTModel(..), SMTResult(..), State(..), incrementInternalCounter)

import Data.SBV.Utils.SExpr
import Data.SBV.Utils.Boolean

import Data.SBV.Control.Types
import Data.SBV.Control.Utils

-- | An Assignment of a model binding
data Assignment = Assign SVal CW

-- Remove one pair of surrounding 'c's, if present
noSurrounding :: Char -> String -> String
noSurrounding c (c':cs@(_:_)) | c == c' && c == last cs  = init cs
noSurrounding _ s                                        = s

-- Remove a pair of surrounding quotes
unQuote :: String -> String
unQuote = noSurrounding '"'

-- Remove a pair of surrounding bars
unBar :: String -> String
unBar = noSurrounding '|'

-- Is this a string? If so, return it, otherwise fail in the Maybe monad.
fromECon :: SExpr -> Maybe String
fromECon (ECon s) = Just s
fromECon _        = Nothing

-- Collect strings appearing, used in 'getOption' only
stringsOf :: SExpr -> [String]
stringsOf (ECon s)      = [s]
stringsOf (ENum (i, _)) = [show i]
stringsOf (EReal   r)   = [show r]
stringsOf (EFloat  f)   = [show f]
stringsOf (EDouble d)   = [show d]
stringsOf (EApp ss)     = concatMap stringsOf ss

-- Sort of a light-hearted show for SExprs, for better consumption at the user level.
serialize :: Bool -> SExpr -> String
serialize removeQuotes = go
  where go (ECon s)      = if removeQuotes then unQuote s else s
        go (ENum (i, _)) = shNN i
        go (EReal   r)   = shNN r
        go (EFloat  f)   = shNN f
        go (EDouble d)   = shNN d
        go (EApp [x])    = go x
        go (EApp ss)     = "(" ++ unwords (map go ss) ++ ")"

        -- be careful with negative number printing in SMT-Lib..
        shNN :: (Show a, Num a, Ord a) => a -> String
        shNN i
          | i < 0 = "(- " ++ show (-i) ++ ")"
          | True  = show i

-- | Ask solver for info.
getInfo :: SMTInfoFlag -> Query SMTInfoResponse
getInfo flag = do
    let cmd = "(get-info " ++ show flag ++ ")"
        bad = unexpected "getInfo" cmd "a valid get-info response" Nothing

        isAllStatistics AllStatistics = True
        isAllStatistics _             = False

        isAllStat = isAllStatistics flag

        grabAllStat k v = (render k, render v)

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
                 EApp (ECon ":authors" : ns)                               -> return $ Resp_Authors (map render ns)
                 EApp [ECon ":error-behavior", ECon "immediate-exit"]      -> return $ Resp_Error ErrorImmediateExit
                 EApp [ECon ":error-behavior", ECon "continued-execution"] -> return $ Resp_Error ErrorContinuedExecution
                 EApp (ECon ":name" : o)                                   -> return $ Resp_Name (render (EApp o))
                 EApp (ECon ":reason-unknown" : o)                         -> return $ Resp_ReasonUnknown (unk o)
                 EApp (ECon ":version" : o)                                -> return $ Resp_Version (render (EApp o))
                 EApp (ECon s : o)                                         -> return $ Resp_InfoKeyword s (map render o)
                 _                                                         -> bad r Nothing

  where render = serialize True

        unk [ECon s] | Just d <- getUR s = d
        unk o                            = UnknownOther (render (EApp o))

        getUR s = map toLower (unQuote s) `lookup` [(map toLower k, d) | (k, d) <- unknownReasons]

        -- As specified in Section 4.1 of the SMTLib document. Note that we're adding the
        -- extra timeout as it is useful in this context.
        unknownReasons = [ ("memout",     UnknownMemOut)
                         , ("incomplete", UnknownIncomplete)
                         , ("timeout",    UnknownTimeOut)
                         ]

-- | Retrieve the value of an 'SMTOption.' The curious function argument is on purpose here,
-- simply pass the constructor name. Example: the call @'getOption' 'ProduceUnsatCores'@ will return
-- either @Nothing@ or @Just (ProduceUnsatCores True)@ or @Just (ProduceUnsatCores False)@.
--
-- Result will be 'Nothing' if the solver does not support this option.
getOption :: (a -> SMTOption) -> Query (Maybe SMTOption)
getOption f = case f undefined of
                 DiagnosticOutputChannel{}   -> askFor "DiagnosticOutputChannel"   ":diagnostic-output-channel"   $ string     DiagnosticOutputChannel
                 ProduceAssertions{}         -> askFor "ProduceAssertions"         ":produce-assertions"          $ bool       ProduceAssertions
                 ProduceAssignments{}        -> askFor "ProduceAssignments"        ":produce-assignments"         $ bool       ProduceAssignments
                 ProduceProofs{}             -> askFor "ProduceProofs"             ":produce-proofs"              $ bool       ProduceProofs
                 ProduceInterpolants{}       -> askFor "ProduceInterpolants"       ":produce-interpolants"        $ bool       ProduceInterpolants
                 ProduceUnsatAssumptions{}   -> askFor "ProduceUnsatAssumptions"   ":produce-unsat-assumptions"   $ bool       ProduceUnsatAssumptions
                 ProduceUnsatCores{}         -> askFor "ProduceUnsatCores"         ":produce-unsat-cores"         $ bool       ProduceUnsatCores
                 RandomSeed{}                -> askFor "RandomSeed"                ":random-seed"                 $ integer    RandomSeed
                 ReproducibleResourceLimit{} -> askFor "ReproducibleResourceLimit" ":reproducible-resource-limit" $ integer    ReproducibleResourceLimit
                 SMTVerbosity{}              -> askFor "SMTVerbosity"              ":verbosity"                   $ integer    SMTVerbosity
                 OptionKeyword nm _          -> askFor ("OptionKeyword" ++ nm)     nm                             $ stringList (OptionKeyword nm)
                 SetLogic{}                  -> error "Data.SBV.Query: SMTLib does not allow querying value of the logic!"
                 -- Not to be confused by getInfo, which is totally irrelevant!
                 SetInfo{}                   -> error "Data.SBV.Query: SMTLib does not allow querying value of meta-info!"

  where askFor sbvName smtLibName continue = do
                let cmd = "(get-option " ++ smtLibName ++ ")"
                    bad = unexpected ("getOption " ++ sbvName) cmd "a valid option value" Nothing

                r <- ask cmd

                parse r bad $ \case ECon "unsupported" -> return Nothing
                                    e                  -> continue e (bad r)

        string c (ECon s) _ = return $ Just $ c s
        string _ e        k = k $ Just ["Expected string, but got: " ++ show (serialize False e)]

        bool c (ENum (0, _)) _ = return $ Just $ c False
        bool c (ENum (1, _)) _ = return $ Just $ c True
        bool _ e             k = k $ Just ["Expected boolean, but got: " ++ show (serialize False e)]

        integer c (ENum (i, _)) _ = return $ Just $ c i
        integer _ e             k = k $ Just ["Expected integer, but got: " ++ show (serialize False e)]

        -- free format, really
        stringList c e _ = return $ Just $ c $ stringsOf e

-- | Get the reason unknown. Only internally used.
getUnknownReason :: Query SMTReasonUnknown
getUnknownReason = do ru <- getInfo ReasonUnknown
                      case ru of
                        Resp_Unsupported     -> return $ UnknownOther "Solver responded: Unsupported."
                        Resp_ReasonUnknown r -> return r
                        -- Shouldn't happen, but just in case:
                        _                    -> error $ "Unexpected reason value received: " ++ show ru

-- | Issue check-sat and get an SMT Result out.
getSMTResult :: Query SMTResult
getSMTResult = do cfg <- getConfig
                  cs  <- checkSat
                  case cs of
                    Unsat -> Unsatisfiable cfg <$> getUnsatCoreIfRequested
                    Sat   -> Satisfiable   cfg <$> getModel
                    Unk   -> Unknown       cfg <$> getUnknownReason

-- | Classify a model based on whether it has unbound objectives or not.
classifyModel :: SMTConfig -> SMTModel -> SMTResult
classifyModel cfg m = case filter (not . isRegularCW . snd) (modelObjectives m) of
                        [] -> Satisfiable cfg m
                        _  -> SatExtField cfg m

-- | Issue check-sat and get results of a lexicographic optimization.
getLexicographicOptResults :: Query SMTResult
getLexicographicOptResults = do cfg <- getConfig
                                cs  <- checkSat
                                case cs of
                                  Unsat -> Unsatisfiable cfg <$> getUnsatCoreIfRequested
                                  Sat   -> classifyModel cfg <$> getModelWithObjectives
                                  Unk   -> Unknown       cfg <$> getUnknownReason
   where getModelWithObjectives = do objectiveValues <- getObjectiveValues
                                     m               <- getModel
                                     return m {modelObjectives = objectiveValues}

-- | Issue check-sat and get results of an independent (boxed) optimization.
getIndependentOptResults :: [String] -> Query [(String, SMTResult)]
getIndependentOptResults objNames = do cfg <- getConfig
                                       cs  <- checkSat

                                       case cs of
                                         Unsat -> getUnsatCoreIfRequested >>= \mbUC -> return [(nm, Unsatisfiable cfg mbUC) | nm <- objNames]
                                         Sat   -> continue (classifyModel cfg)
                                         Unk   -> do ur <- Unknown cfg <$> getUnknownReason
                                                     return [(nm, ur) | nm <- objNames]

  where continue classify = do objectiveValues <- getObjectiveValues
                               nms <- zipWithM getIndependentResult [0..] objNames
                               return [(n, classify (m {modelObjectives = objectiveValues})) | (n, m) <- nms]

        getIndependentResult :: Int -> String -> Query (String, SMTModel)
        getIndependentResult i s = do m <- getModelAtIndex (Just i)
                                      return (s, m)

-- | Construct a pareto-front optimization result
getParetoOptResults :: Maybe Int -> Query (Bool, [SMTResult])
getParetoOptResults (Just i)
        | i <= 0             = return (True, [])
getParetoOptResults mbN      = do cfg <- getConfig
                                  cs  <- checkSat

                                  case cs of
                                    Unsat -> return (False, [])
                                    Sat   -> continue (classifyModel cfg)
                                    Unk   -> do ur <- getUnknownReason
                                                return (False, [ProofError cfg [show ur]])

  where continue classify = do m <- getModel
                               (limReached, fronts) <- getParetoFronts (subtract 1 <$> mbN) [m]
                               return (limReached, reverse (map classify fronts))

        getParetoFronts :: Maybe Int -> [SMTModel] -> Query (Bool, [SMTModel])
        getParetoFronts (Just i) sofar | i <= 0 = return (True, sofar)
        getParetoFronts mbi      sofar          = do cs <- checkSat
                                                     let more = getModel >>= \m -> getParetoFronts (subtract 1 <$> mbi) (m : sofar)
                                                     case cs of
                                                       Unsat -> return (False, sofar)
                                                       Sat   -> more
                                                       Unk   -> more

-- | Collect model values. It is implicitly assumed that we are in a check-sat
-- context. See 'getSMTResult' for a variant that issues a check-sat first and
-- returns an 'SMTResult'.
getModel :: Query SMTModel
getModel = getModelAtIndex Nothing

-- | Get a model stored at an index. This is likely very Z3 specific!
getModelAtIndex :: Maybe Int -> Query SMTModel
getModelAtIndex mbi = do
             State{runMode} <- get
             cfg   <- getConfig
             inps  <- getQuantifiedInputs
             obsvs <- getObservables
             rm    <- io $ readIORef runMode
             let vars :: [NamedSymVar]
                 vars = case rm of
                          m@CodeGen         -> error $ "SBV.getModel: Model is not available in mode: " ++ show m
                          m@Concrete        -> error $ "SBV.getModel: Model is not available in mode: " ++ show m
                          SMTMode _ isSAT _ -> -- for "sat", display the prefix existentials. for "proof", display the prefix universals
                                               let allModelInputs = if isSAT then takeWhile ((/= ALL) . fst) inps
                                                                             else takeWhile ((== ALL) . fst) inps

                                                   -- are we inside a quantifier
                                                   insideQuantifier = length allModelInputs < length inps

                                                   -- observables are only meaningful if we're not in a quantified context
                                                   allPrefixObservables | insideQuantifier = []
                                                                        | True             = [(EX, (sw, nm)) | (nm, sw) <- obsvs]

                                                   sortByNodeId :: [NamedSymVar] -> [NamedSymVar]
                                                   sortByNodeId = sortBy (compare `on` (\(SW _ n, _) -> n))

                                               in sortByNodeId [nv | (_, nv@(_, n)) <- allModelInputs ++ allPrefixObservables, not (isNonModelVar cfg n)]

             assocs <- mapM (\(sw, n) -> (n, ) <$> getValueCW mbi sw) vars

             return SMTModel { modelObjectives = []
                             , modelAssocs     = assocs
                             }

-- | Just after a check-sat is issued, collect objective values. Used
-- internally only, not exposed to the user.
getObjectiveValues :: Query [(String, GeneralizedCW)]
getObjectiveValues = do let cmd = "(get-objectives)"

                            bad = unexpected "getObjectiveValues" cmd "a list of objective values" Nothing

                        r <- ask cmd

                        inputs <- map snd <$> getQuantifiedInputs

                        parse r bad $ \case EApp (ECon "objectives" : es) -> catMaybes <$> mapM (getObjValue (bad r) inputs) es
                                            _                             -> bad r Nothing

  where -- | Parse an objective value out.
        getObjValue :: (forall a. Maybe [String] -> Query a) -> [NamedSymVar] -> SExpr -> Query (Maybe (String, GeneralizedCW))
        getObjValue bailOut inputs expr =
                case expr of
                  EApp [_]                                       -> return Nothing            -- Happens when a soft-assertion has no associated group.
                  EApp [ECon nm, v]                              -> locate nm v               -- Regular case
                  EApp [EApp [ECon "bvadd", ECon nm, ENum _], v] -> locate nm v               -- Happens when we "adjust" a signed-bounded objective
                  _                                              -> dontUnderstand (show expr)

          where locate nm v = case listToMaybe [p | p@(sw, _) <- inputs, show sw == nm] of
                                Nothing               -> return Nothing -- Happens when the soft assertion has a group-id that's not one of the input names
                                Just (sw, actualName) -> grab sw v >>= \val -> return $ Just (actualName, val)

                dontUnderstand s = bailOut $ Just [ "Unable to understand solver output."
                                                  , "While trying to process: " ++ s
                                                  ]

                grab :: SW -> SExpr -> Query GeneralizedCW
                grab s topExpr
                  | Just v <- recoverKindedValue k topExpr = return $ RegularCW v
                  | True                                   = ExtendedCW <$> cvt (simplify topExpr)
                  where k = kindOf s

                        -- Convert to an extended expression. Hopefully complete!
                        cvt :: SExpr -> Query ExtCW
                        cvt (ECon "oo")                    = return $ Infinite  k
                        cvt (ECon "epsilon")               = return $ Epsilon   k
                        cvt (EApp [ECon "interval", x, y]) =          Interval  <$> cvt x <*> cvt y
                        cvt (ENum    (i, _))               = return $ BoundedCW $ mkConstCW k i
                        cvt (EReal   r)                    = return $ BoundedCW $ CW k $ CWAlgReal r
                        cvt (EFloat  f)                    = return $ BoundedCW $ CW k $ CWFloat   f
                        cvt (EDouble d)                    = return $ BoundedCW $ CW k $ CWDouble  d
                        cvt (EApp [ECon "+", x, y])        =          AddExtCW <$> cvt x <*> cvt y
                        cvt (EApp [ECon "*", x, y])        =          MulExtCW <$> cvt x <*> cvt y
                        -- Nothing else should show up, hopefully!
                        cvt e = dontUnderstand (show e)

                        -- drop the pesky to_real's that Z3 produces.. Cool but useless.
                        simplify :: SExpr -> SExpr
                        simplify (EApp [ECon "to_real", n]) = n
                        simplify (EApp xs)                  = EApp (map simplify xs)
                        simplify e                          = e

-- | Check for satisfiability, under the given conditions. Similar to 'checkSat' except it allows making
-- further assumptions as captured by the first argument of booleans. (Also see 'checkSatAssumingWithUnsatisfiableSet'
-- for a variant that returns the subset of the given assumptions that led to the 'Unsat' conclusion.)
checkSatAssuming :: [SBool] -> Query CheckSatResult
checkSatAssuming sBools = fst <$> checkSatAssumingHelper False sBools

-- | Check for satisfiability, under the given conditions. Returns the unsatisfiable
-- set of assumptions. Similar to 'checkSat' except it allows making further assumptions
-- as captured by the first argument of booleans. If the result is 'Unsat', the user will
-- also receive a subset of the given assumptions that led to the 'Unsat' conclusion. Note
-- that while this set will be a subset of the inputs, it is not necessarily guaranteed to be minimal.
--
-- You must have arranged for the production of unsat assumptions
-- first (/via/ @'setOption' $ 'ProduceUnsatAssumptions' 'True'@)
-- for this call to not error out!
--
-- Usage note: 'getUnsatCore' is usually easier to use than 'checkSatAssumingWithUnsatisfiableSet', as it
-- allows the use of named assertions, as obtained by 'namedAssert'. If 'getUnsatCore'
-- fills your needs, you should definitely prefer it over 'checkSatAssumingWithUnsatisfiableSet'.
checkSatAssumingWithUnsatisfiableSet :: [SBool] -> Query (CheckSatResult, Maybe [SBool])
checkSatAssumingWithUnsatisfiableSet = checkSatAssumingHelper True

-- | Helper for the two variants of checkSatAssuming we have. Internal only.
checkSatAssumingHelper :: Bool -> [SBool] -> Query (CheckSatResult, Maybe [SBool])
checkSatAssumingHelper getAssumptions sBools = do
        -- sigh.. SMT-Lib requires the values to be literals only. So, create proxies.
        let mkAssumption st = do swsOriginal <- mapM (\sb -> do sw <- sbvToSW st sb
                                                                return (sw, sb)) sBools

                                 -- drop duplicates and trues
                                 let swbs = [p | p@(sw, _) <- nubBy ((==) `on` fst) swsOriginal, sw /= trueSW]

                                 -- get a unique proxy name for each
                                 uniqueSWBs <- mapM (\(sw, sb) -> do unique <- incrementInternalCounter st
                                                                     return (sw, (unique, sb))) swbs

                                 let translate (sw, (unique, sb)) = (nm, decls, (proxy, sb))
                                        where nm    = show sw
                                              proxy = "__assumption_proxy_" ++ nm ++ "_" ++ show unique
                                              decls = [ "(declare-const " ++ proxy ++ " Bool)"
                                                      , "(assert (= " ++ proxy ++ " " ++ nm ++ "))"
                                                      ]

                                 return $ map translate uniqueSWBs

        assumptions <- inNewContext mkAssumption

        let (origNames, declss, proxyMap) = unzip3 assumptions

        let cmd = "(check-sat-assuming (" ++ unwords (map fst proxyMap) ++ "))"
            bad = unexpected "checkSatAssuming" cmd "one of sat/unsat/unknown"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       setOption $ ProduceUnsatAssumptions True"
                                  , ""
                                  , "to tell the solver to produce unsat assumptions."
                                  ]

        mapM_ (send True) $ concat declss
        r <- ask cmd

        let grabUnsat
             | getAssumptions = do as <- getUnsatAssumptions origNames proxyMap
                                   return (Unsat, Just as)
             | True           = return (Unsat, Nothing)

        parse r bad $ \case ECon "sat"     -> return (Sat, Nothing)
                            ECon "unsat"   -> grabUnsat
                            ECon "unknown" -> return (Unk, Nothing)
                            _              -> bad r Nothing

-- | The current assertion stack depth, i.e., #push - #pops after start. Always non-negative.
getAssertionStackDepth :: Query Int
getAssertionStackDepth = queryAssertionStackDepth <$> getQueryState

-- | Upon a pop, we need to restore all arrays and tables. See: https://github.com/LeventErkok/sbv/issues/374
restoreTablesAndArrays :: Query ()
restoreTablesAndArrays = do st <- get
                            qs <- getQueryState

                            case queryTblArrPreserveIndex qs of
                              Nothing       -> return ()
                              Just (tc, ac) -> do tCount <- M.size  <$> (io . readIORef) (rtblMap   st)
                                                  aCount <- IM.size <$> (io . readIORef) (rArrayMap st)

                                                  let tInits = [ "table"  ++ show i ++ "_initializer" | i <- [tc .. tCount - 1]]
                                                      aInits = [ "array_" ++ show i ++ "_initializer" | i <- [ac .. aCount - 1]]
                                                      inits  = tInits ++ aInits

                                                  case inits of
                                                    []  -> return ()   -- Nothing to do
                                                    [x] -> send True $ "(assert " ++ x ++ ")"
                                                    xs  -> send True $ "(assert (and " ++ unwords xs ++ "))"

-- | Upon a push, record the cut-off point for table and array restoration, if we haven't already
recordTablesAndArrayCutOff :: Query ()
recordTablesAndArrayCutOff = do st <- get
                                qs <- getQueryState

                                case queryTblArrPreserveIndex qs of
                                  Just _  -> return () -- already recorded, nothing to do
                                  Nothing -> do tCount <- M.size  <$> (io . readIORef) (rtblMap   st)
                                                aCount <- IM.size <$> (io . readIORef) (rArrayMap st)

                                                modifyQueryState $ \s -> s {queryTblArrPreserveIndex = Just (tCount, aCount)}

-- | Run the query in a new assertion stack. That is, we push the context, run the query
-- commands, and pop it back.
inNewAssertionStack :: Query a -> Query a
inNewAssertionStack q = do push 1
                           r <- q
                           pop 1
                           return r

-- | Push the context, entering a new one. Pushes multiple levels if /n/ > 1.
push :: Int -> Query ()
push i
 | i <= 0 = error $ "Data.SBV: push requires a strictly positive level argument, received: " ++ show i
 | True   = do depth <- getAssertionStackDepth
               send True $ "(push " ++ show i ++ ")"
               recordTablesAndArrayCutOff
               modifyQueryState $ \s -> s{queryAssertionStackDepth = depth + i}

-- | Pop the context, exiting a new one. Pops multiple levels if /n/ > 1. It's an error to pop levels that don't exist.
pop :: Int -> Query ()
pop i
 | i <= 0 = error $ "Data.SBV: pop requires a strictly positive level argument, received: " ++ show i
 | True   = do depth <- getAssertionStackDepth
               if i > depth
                  then error $ "Data.SBV: Illegally trying to pop " ++ shl i ++ ", at current level: " ++ show depth
                  else do QueryState{queryConfig} <- getQueryState
                          if not (supportsGlobalDecls (capabilities (solver queryConfig)))
                             then error $ unlines [ ""
                                                  , "*** Data.SBV: Backend solver does not support global-declarations."
                                                  , "***           Hence, calls to 'pop' are not supported."
                                                  , "***"
                                                  , "*** Request this as a feature for the underlying solver!"
                                                  ]
                             else do send True $ "(pop " ++ show i ++ ")"
                                     restoreTablesAndArrays
                                     modifyQueryState $ \s -> s{queryAssertionStackDepth = depth - i}
   where shl 1 = "one level"
         shl n = show n ++ " levels"

-- | Search for a result via a sequence of case-splits, guided by the user. If one of
-- the conditions lead to a satisfiable result, returns @Just@ that result. If none of them
-- do, returns @Nothing@. Note that we automatically generate a coverage case and search
-- for it automatically as well. In that latter case, the string returned will be "Coverage".
-- The first argument controls printing progress messages  See "Documentation.SBV.Examples.Queries.CaseSplit"
-- for an example use case.
caseSplit :: Bool -> [(String, SBool)] -> Query (Maybe (String, SMTResult))
caseSplit printCases cases = do cfg <- getConfig
                                go cfg (cases ++ [("Coverage", bnot (bOr (map snd cases)))])
  where msg = when printCases . io . putStrLn

        go _ []            = return Nothing
        go cfg ((n,c):ncs) = do let notify s = msg $ "Case " ++ n ++ ": " ++ s

                                notify "Starting"
                                r <- checkSatAssuming [c]

                                case r of
                                  Unsat -> do notify "Unsatisfiable"
                                              go cfg ncs

                                  Sat   -> do notify "Satisfiable"
                                              res <- Satisfiable cfg <$> getModel
                                              return $ Just (n, res)

                                  Unk   -> do notify "Unknown"
                                              res <- Unknown cfg <$> getUnknownReason
                                              return $ Just (n, res)

-- | Reset the solver, by forgetting all the assertions. However, bindings are kept as is,
-- as opposed to 'reset'. Use this variant to clean-up the solver state while leaving the bindings
-- intact. Pops all assertion levels. Declarations and definitions resulting from the 'setLogic'
-- command are unaffected. Note that SBV implicitly uses global-declarations, so bindings will remain intact.
resetAssertions :: Query ()
resetAssertions = do send True "(reset-assertions)"
                     modifyQueryState $ \s -> s{queryAssertionStackDepth = 0}

-- | Echo a string. Note that the echoing is done by the solver, not by SBV.
echo :: String -> Query ()
echo s = do let cmd = "(echo \"" ++ concatMap sanitize s ++ "\")"

            -- we send the command, but otherwise ignore the response
            -- note that 'send True/False' would be incorrect here. 'send True' would
            -- require a success response. 'send False' would fail to consume the
            -- output. But 'ask' does the right thing! It gets "some" response,
            -- and forgets about it immediately.
            _ <- ask cmd

            return ()
  where sanitize '"'  = "\"\""  -- quotes need to be duplicated
        sanitize c    = [c]

-- | Exit the solver. This action will cause the solver to terminate. Needless to say,
-- trying to communicate with the solver after issuing "exit" will simply fail.
exit :: Query ()
exit = do send True "(exit)"
          modifyQueryState $ \s -> s{queryAssertionStackDepth = 0}

-- | Retrieve the unsat-core. Note you must have arranged for
-- unsat cores to be produced first (/via/ @'setOption' $ 'ProduceUnsatCores' 'True'@)
-- for this call to not error out!
getUnsatCore :: Query [String]
getUnsatCore = do
        let cmd = "(get-unsat-core)"
            bad = unexpected "getUnsatCore" cmd "an unsat-core response"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       setOption $ ProduceUnsatCores True"
                                  , ""
                                  , "so the solver will be ready to compute unsat cores,"
                                  , "and that there is a model by first issuing a 'checkSat' call."
                                  ]

        r <- ask cmd

        parse r bad $ \case
           EApp es | Just xs <- mapM fromECon es -> return $ map unBar xs
           _                                     -> bad r Nothing

-- | Retrieve the unsat core if it was asked for in the configuration
getUnsatCoreIfRequested :: Query (Maybe [String])
getUnsatCoreIfRequested = do
        cfg <- getConfig
        if or [b | ProduceUnsatCores b <- solverSetOptions cfg]
           then Just <$> getUnsatCore
           else return Nothing

-- | Retrieve the proof. Note you must have arranged for
-- proofs to be produced first (/via/ @'setOption' $ 'ProduceProofs' 'True'@)
-- for this call to not error out!
--
-- A proof is simply a 'String', as returned by the solver. In the future, SBV might
-- provide a better datatype, depending on the use cases. Please get in touch if you
-- use this function and can suggest a better API.
getProof :: Query String
getProof = do
        let cmd = "(get-proof)"
            bad = unexpected "getProof" cmd "a get-proof response"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       setOption $ ProduceProofs True"
                                  , ""
                                  , "to make sure the solver is ready for producing proofs,"
                                  , "and that there is a proof by first issuing a 'checkSat' call."
                                  ]


        r <- ask cmd

        -- we only care about the fact that we can parse the output, so the
        -- result of parsing is ignored.
        parse r bad $ \_ -> return r

-- | Retrieve an interpolant after an 'Unsat' result is obtained. Note you must have arranged for
-- interpolants to be produced first (/via/ @'setOption' $ 'ProduceInterpolants' 'True'@)
-- for this call to not error out!
--
-- To get an interpolant for a pair of formulas @A@ and @B@, use a 'constrainWithAttribute' call to attach
-- interplation groups to @A@ and @B@. Then call 'getInterpolant' @[\"A\"]@, assuming those are the names
-- you gave to the formulas in the @A@ group.
--
-- An interpolant for @A@ and @B@ is a formula @I@ such that:
--
-- @
--        A ==> I
--    and B ==> not I
-- @
--
-- That is, it's evidence that @A@ and @B@ cannot be true together
-- since @A@ implies @I@ but @B@ implies @not I@; establishing that @A@ and @B@ cannot
-- be satisfied at the same time. Furthermore, @I@ will have only the symbols that are common
-- to @A@ and @B@.
--
-- N.B. As of Z3 version 4.8.0; Z3 no longer supports interpolants. Use the MathSAT backend for extracting
-- interpolants. See 'Documentation.SBV.Examples.Queries.Interpolants' for an example.
getInterpolant :: [String] -> Query String
getInterpolant fs
  | null fs
  = error "SBV.getInterpolant requires at least one marked constraint, received none!"
  | True
  = do let bar s = '|' : s ++ "|"
           cmd = "(get-interpolant (" ++ unwords (map bar fs) ++ "))"
           bad = unexpected "getInterpolant" cmd "a get-interpolant response"
                          $ Just [ "Make sure you use:"
                                 , ""
                                 , "       setOption $ ProduceInterpolants True"
                                 , ""
                                 , "to make sure the solver is ready for producing interpolants,"
                                 , "and that you have used the proper attributes using the"
                                 , "constrainWithAttribute function."
                                 ]

       r <- ask cmd

       parse r bad $ \e -> return $ serialize False e

-- | Retrieve assertions. Note you must have arranged for
-- assertions to be available first (/via/ @'setOption' $ 'ProduceAssertions' 'True'@)
-- for this call to not error out!
--
-- Note that the set of assertions returned is merely a list of strings, just like the
-- case for 'getProof'. In the future, SBV might provide a better datatype, depending
-- on the use cases. Please get in touch if you use this function and can suggest
-- a better API.
getAssertions :: Query [String]
getAssertions = do
        let cmd = "(get-assertions)"
            bad = unexpected "getAssertions" cmd "a get-assertions response"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       setOption $ ProduceAssertions True"
                                  , ""
                                  , "to make sure the solver is ready for producing assertions."
                                  ]

            render = serialize False

        r <- ask cmd

        parse r bad $ \pe -> case pe of
                                EApp xs -> return $ map render xs
                                _       -> return [render pe]

-- | Retrieve the assignment. This is a lightweight version of 'getValue', where the
-- solver returns the truth value for all named subterms of type 'Bool'.
getAssignment :: Query [(String, Bool)]
getAssignment = do
        let cmd = "(get-assignment)"
            bad = unexpected "getAssignment" cmd "a get-assignment response"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       setOption $ ProduceAssignments True"
                                  , ""
                                  , "to make sure the solver is ready for producing assignments,"
                                  , "and that there is a model by first issuing a 'checkSat' call."
                                  ]

            -- we're expecting boolean assignment to labels, essentially
            grab (EApp [ECon s, ENum (0, _)]) = Just (unQuote s, False)
            grab (EApp [ECon s, ENum (1, _)]) = Just (unQuote s, True)
            grab _                            = Nothing

        r <- ask cmd

        parse r bad $ \case EApp ps | Just vs <- mapM grab ps -> return vs
                            _                                 -> bad r Nothing

-- | Make an assignment. The type 'Assignment' is abstract, the result is typically passed
-- to 'mkSMTResult':
--
-- @ mkSMTResult [ a |-> 332
--             , b |-> 2.3
--             , c |-> True
--             ]
-- @
--
-- End users should use 'getModel' for automatically constructing models from the current solver state.
-- However, an explicit 'Assignment' might be handy in complex scenarios where a model needs to be
-- created manually.
infix 1 |->
(|->) :: SymWord a => SBV a -> a -> Assignment
SBV a |-> v = case literal v of
                SBV (SVal _ (Left cw)) -> Assign a cw
                r                      -> error $ "Data.SBV: Impossible happened in |->: Cannot construct a CW with literal: " ++ show r

-- | Produce the query result from an assignment.
mkSMTResult :: [Assignment] -> Query SMTResult
mkSMTResult asgns = do
             QueryState{queryConfig} <- getQueryState
             inps <- getQuantifiedInputs

             let grabValues st = do let extract (Assign s n) = sbvToSW st (SBV s) >>= \sw -> return (sw, n)

                                    modelAssignment <- mapM extract asgns

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
                                                            , "***"
                                                            ]
                                                         ++ [ align misTag ++ intercalate ", "  missing | not (null missing)]
                                                         ++ [ align extTag ++ intercalate ", "  extra   | not (null extra)  ]
                                                         ++ [ align dupTag ++ intercalate ", "  dup     | not (null dup)    ]
                                                         ++ [ "***"
                                                            , "*** Data.SBV: Check your query result construction!"
                                                            ]

                                    let findName s = case [nm | (_, (i, nm)) <- inps, s == i] of
                                                        [nm] -> nm
                                                        []   -> error "*** Data.SBV: Impossible happened: Cannot find " ++ show s ++ " in the input list"
                                                        nms  -> error $ unlines [ ""
                                                                                , "*** Data.SBV: Impossible happened: Multiple matches for: " ++ show s
                                                                                , "***   Candidates: " ++ unwords nms
                                                                                ]

                                    return [(findName s, n) | (s, n) <- modelAssignment]

             assocs <- inNewContext grabValues

             let m = SMTModel { modelObjectives = []
                              , modelAssocs     = assocs
                              }

             return $ Satisfiable queryConfig m
