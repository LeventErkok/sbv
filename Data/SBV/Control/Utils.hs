-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control.Utils
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Query related utils.
-----------------------------------------------------------------------------

{-# LANGUAGE    BangPatterns          #-}
{-# LANGUAGE    DefaultSignatures     #-}
{-# LANGUAGE    LambdaCase            #-}
{-# LANGUAGE    NamedFieldPuns        #-}
{-# LANGUAGE    ScopedTypeVariables   #-}
{-# LANGUAGE    TupleSections         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Data.SBV.Control.Utils (
       io
     , ask, send, getValue, getUninterpretedValue, getValueCW, getUnsatAssumptions, SMTValue(..)
     , getQueryState, modifyQueryState, getConfig, getObjectives, getSBVAssertions, getSBVPgm, getQuantifiedInputs
     , checkSat, checkSatUsing, getAllSatResult
     , inNewContext, freshVar, freshVar_
     , parse
     , unexpected
     , timeout
     , queryDebug
     , retrieveResponse
     , runProofOn
     ) where

import Data.List  (sortBy, elemIndex, partition, groupBy, tails)

import Data.Char     (isPunctuation, isSpace)
import Data.Ord      (comparing)
import Data.Function (on)

import Data.Int
import Data.Word

import qualified Data.Map    as Map
import qualified Data.IntMap as IMap

import Control.Monad            (unless)
import Control.Monad.State.Lazy (get, liftIO)

import Data.IORef (readIORef, writeIORef)

import Data.Time (getZonedTime)

import Data.SBV.Core.Data     ( SW(..), CW(..), SBV, AlgReal, sbvToSW, kindOf, Kind(..)
                              , HasKind(..), mkConstCW, CWVal(..), SMTResult(..)
                              , NamedSymVar, SMTConfig(..), Query, SMTModel(..)
                              , QueryState(..), SVal(..), Quantifier(..), cache
                              , newExpr, SBVExpr(..), Op(..), FPOp(..), SBV(..)
                              , SolverContext(..), SBool, Objective(..), SolverCapabilities(..), capabilities
                              , Result(..), SMTProblem(..), trueSW, SymWord(..), SBVPgm(..)
                              )
import Data.SBV.Core.Symbolic (IncState(..), withNewIncState, State(..), svToSW, registerLabel, svMkSymVar)

import Data.SBV.Core.AlgReals   (mergeAlgReals)
import Data.SBV.Core.Operations (svNot, svNotEqual, svOr)

import Data.SBV.SMT.SMTLib  (toIncSMTLib, toSMTLib)
import Data.SBV.SMT.Utils   (showTimeoutValue, annotateWithName, alignDiagnostic, alignPlain, debug, mergeSExpr)

import Data.SBV.Utils.SExpr
import Data.SBV.Control.Types

import qualified Data.Set as Set (toList)

import GHC.Stack

-- | 'Query' as a 'SolverContext'.
instance SolverContext Query where
   constrain          = addQueryConstraint Nothing
   namedConstraint nm = addQueryConstraint (Just nm)

   setOption o
     | isStartModeOption o = error $ unlines [ ""
                                             , "*** Data.SBV: '" ++ show o ++ "' can only be set at start-up time."
                                             , "*** Hint: Move the call to 'setOption' before the query."
                                             ]
     | True                = send True $ setSMTOption o

-- | Adding a constraint, possibly named. Only used internally.
-- Use 'constrain' and 'namedConstraint' from user programs.
addQueryConstraint :: Maybe String -> SBool -> Query ()
addQueryConstraint mbNm b = do sw <- inNewContext (\st -> do maybe (return ()) (registerLabel st) mbNm
                                                             sbvToSW st b)
                               send True $ "(assert " ++ mkNamed mbNm (show sw)  ++ ")"
   where mkNamed Nothing   s = s
         mkNamed (Just nm) s = annotateWithName nm s


-- | Get the current configuration
getConfig :: Query SMTConfig
getConfig = queryConfig <$> getQueryState

-- | Get the objectives
getObjectives :: Query [Objective (SW, SW)]
getObjectives = do State{rOptGoals} <- get
                   io $ reverse <$> readIORef rOptGoals

-- | Get the program
getSBVPgm :: Query SBVPgm
getSBVPgm = do State{spgm} <- get
               io $ readIORef spgm

-- | Get the assertions put in via 'sAssert'
getSBVAssertions :: Query [(String, Maybe CallStack, SW)]
getSBVAssertions = do State{rAsserts} <- get
                      io $ reverse <$> readIORef rAsserts

-- | Perform an arbitrary IO action.
io :: IO a -> Query a
io = liftIO

-- | Sync-up the external solver with new context we have generated
syncUpSolver :: IncState -> Query ()
syncUpSolver is = do
        cfg <- getConfig
        ls  <- io $ do let swap  (a, b)        = (b, a)
                           swapc ((_, a), b)   = (b, a)
                           cmp   (a, _) (b, _) = a `compare` b
                           arrange (i, (at, rt, es)) = ((i, at, rt), es)
                       inps  <- reverse <$> readIORef (rNewInps is)
                       ks    <- readIORef (rNewKinds is)
                       cnsts <- sortBy cmp . map swapc . Map.toList <$> readIORef (rNewConsts is)
                       arrs  <- IMap.toAscList <$> readIORef (rNewArrs is)
                       tbls  <- (map arrange . sortBy cmp . map swap . Map.toList) <$> readIORef (rNewTbls is)
                       as    <- readIORef (rNewAsgns is)
                       return $ toIncSMTLib cfg inps ks cnsts arrs tbls as cfg
        mapM_ (send True) $ mergeSExpr ls

-- | Retrieve the query context
getQueryState :: Query QueryState
getQueryState = do state <- get
                   mbQS  <- io $ readIORef (queryState state)
                   case mbQS of
                     Nothing -> error $ unlines [ ""
                                                , "*** Data.SBV: Impossible happened: Query context required in a non-query mode."
                                                , "Please report this as a bug!"
                                                ]
                     Just qs -> return qs

-- | Modify the query state
modifyQueryState :: (QueryState -> QueryState) -> Query ()
modifyQueryState f = do state <- get
                        mbQS  <- io $ readIORef (queryState state)
                        case mbQS of
                          Nothing -> error $ unlines [ ""
                                                     , "*** Data.SBV: Impossible happened: Query context required in a non-query mode."
                                                     , "Please report this as a bug!"
                                                     ]
                          Just qs -> let fqs = f qs
                                     in fqs `seq` io $ writeIORef (queryState state) $ Just fqs

-- | Execute in a new incremental context
inNewContext :: (State -> IO a) -> Query a
inNewContext act = do st <- get
                      (is, r) <- io $ withNewIncState st act
                      syncUpSolver is
                      return r

-- | Similar to 'freshVar', except creates unnamed variable.
freshVar_ :: forall a. SymWord a => Query (SBV a)
freshVar_ = inNewContext $ fmap SBV . svMkSymVar (Just EX) k Nothing
  where k = kindOf (undefined :: a)

-- | Create a fresh variable in query mode. You should prefer
-- creating input variables using 'sBool', 'sInt32', etc., which act
-- as primary inputs to the model and can be existential or universal.
-- Use 'freshVar' only in query mode for anonymous temporary variables.
-- Such variables are always existential. Note that 'freshVar' should hardly be
-- needed: Your input variables and symbolic expressions should suffice for
-- most major use cases.
freshVar :: forall a. SymWord a => String -> Query (SBV a)
freshVar nm = inNewContext $ fmap SBV . svMkSymVar (Just EX) k (Just nm)
  where k = kindOf (undefined :: a)

-- | Internal diagnostic messages.
queryDebug :: [String] -> Query ()
queryDebug msgs = do QueryState{queryConfig} <- getQueryState
                     io $ debug queryConfig msgs

-- | Send a string to the solver, and return the response
ask :: String -> Query String
ask s = do QueryState{queryAsk, queryTimeOutValue} <- getQueryState

           case queryTimeOutValue of
             Nothing -> queryDebug ["[SEND] " `alignPlain` s]
             Just i  -> queryDebug ["[SEND, TimeOut: " ++ showTimeoutValue i ++ "] " `alignPlain` s]
           r <- io $ queryAsk queryTimeOutValue s
           queryDebug ["[RECV] " `alignPlain` r]

           return r

-- | Send a string to the solver. If the first argument is 'True', we will require
-- a "success" response as well. Otherwise, we'll fire and forget.
send :: Bool -> String -> Query ()
send requireSuccess s = do

            QueryState{queryAsk, querySend, queryConfig, queryTimeOutValue} <- getQueryState

            if requireSuccess && supportsCustomQueries (capabilities (solver queryConfig))
               then do r <- io $ queryAsk queryTimeOutValue s

                       case words r of
                         ["success"] -> queryDebug ["[GOOD] " `alignPlain` s]
                         _           -> do case queryTimeOutValue of
                                             Nothing -> queryDebug ["[FAIL] " `alignPlain` s]
                                             Just i  -> queryDebug [("[FAIL, TimeOut: " ++ showTimeoutValue i ++ "]  ") `alignPlain` s]


                                           let cmd = case words (dropWhile (\c -> isSpace c || isPunctuation c) s) of
                                                       (c:_) -> c
                                                       _     -> "Command"

                                           unexpected cmd s "success" Nothing r Nothing

               else io $ querySend queryTimeOutValue s  -- fire and forget. if you use this, you're on your own!

-- | Retrieve a responses from the solver until it produces a synchronization tag. We make the tag
-- unique by attaching a time stamp, so no need to worry about getting the wrong tag unless it happens
-- in the very same picosecond! We return multiple valid s-expressions till the solver responds with the tag.
-- Should only be used for internal tasks or when we want to synchronize communications, and not on a
-- regular basis! Use 'send'/'ask' for that purpose. This comes in handy, however, when solvers respond
-- multiple times as in optimization for instance, where we both get a check-sat answer and some objective values.
retrieveResponse :: String -> Maybe Int -> Query [String]
retrieveResponse userTag mbTo = do
             ts  <- io (show <$> getZonedTime)

             let synchTag = show $ userTag ++ " (at: " ++ ts ++ ")"
                 cmd = "(echo " ++ synchTag ++ ")"

             queryDebug ["[SYNC] Attempting to synchronize with tag: " ++ synchTag]

             send False cmd

             QueryState{queryRetrieveResponse} <- getQueryState

             let loop sofar = do
                  s <- io $ queryRetrieveResponse mbTo

                  -- strictly speaking SMTLib requires solvers to print quotes around
                  -- echo'ed strings, but they don't always do. Accommodate for that
                  -- here, though I wish we didn't have to.
                  if s == synchTag || show s == synchTag
                     then do queryDebug ["[SYNC] Synchronization achieved using tag: " ++ synchTag]
                             return $ reverse sofar
                     else do queryDebug ["[RECV] " `alignPlain` s]
                             loop (s : sofar)

             loop []

-- | A class which allows for sexpr-conversion to values
class SMTValue a where
  sexprToVal :: SExpr -> Maybe a

  default sexprToVal :: Read a => SExpr -> Maybe a
  sexprToVal (ECon c) = case reads c of
                          [(v, "")] -> Just v
                          _         -> Nothing
  sexprToVal _        = Nothing

-- | Integral values are easy to convert:
fromIntegralToVal :: Integral a => SExpr -> Maybe a
fromIntegralToVal (ENum (i, _)) = Just $ fromIntegral i
fromIntegralToVal _             = Nothing

instance SMTValue Int8    where sexprToVal = fromIntegralToVal
instance SMTValue Int16   where sexprToVal = fromIntegralToVal
instance SMTValue Int32   where sexprToVal = fromIntegralToVal
instance SMTValue Int64   where sexprToVal = fromIntegralToVal
instance SMTValue Word8   where sexprToVal = fromIntegralToVal
instance SMTValue Word16  where sexprToVal = fromIntegralToVal
instance SMTValue Word32  where sexprToVal = fromIntegralToVal
instance SMTValue Word64  where sexprToVal = fromIntegralToVal
instance SMTValue Integer where sexprToVal = fromIntegralToVal

instance SMTValue Float where
   sexprToVal (EFloat f) = Just f
   sexprToVal _          = Nothing

instance SMTValue Double where
   sexprToVal (EDouble f) = Just f
   sexprToVal _           = Nothing

instance SMTValue Bool where
   sexprToVal (ENum (1, _)) = Just True
   sexprToVal (ENum (0, _)) = Just False
   sexprToVal _             = Nothing

instance SMTValue AlgReal where
   sexprToVal (EReal a) = Just a
   sexprToVal _         = Nothing

-- | Get the value of a term.
getValue :: SMTValue a => SBV a -> Query a
getValue s = do sw <- inNewContext (`sbvToSW` s)
                let nm  = show sw
                    cmd = "(get-value (" ++ nm ++ "))"
                    bad = unexpected "getValue" cmd "a model value" Nothing
                r <- ask cmd
                parse r bad $ \case EApp [EApp [ECon o,  v]] | o == show sw -> case sexprToVal v of
                                                                                 Nothing -> bad r Nothing
                                                                                 Just c  -> return c
                                    _                                       -> bad r Nothing

-- | Get the value of an uninterpreted sort, as a String
getUninterpretedValue :: HasKind a => SBV a -> Query String
getUninterpretedValue s =
        case kindOf s of
          KUserSort _ (Left _) -> do sw <- inNewContext (`sbvToSW` s)

                                     let nm  = show sw
                                         cmd = "(get-value (" ++ nm ++ "))"
                                         bad = unexpected "getValue" cmd "a model value" Nothing

                                     r <- ask cmd

                                     parse r bad $ \case EApp [EApp [ECon o,  ECon v]] | o == show sw -> return v
                                                         _                                             -> bad r Nothing

          k                    -> error $ unlines [""
                                                  , "*** SBV.getUninterpretedValue: Called on an 'interpreted' kind"
                                                  , "*** "
                                                  , "***    Kind: " ++ show k
                                                  , "***    Hint: Use 'getValue' to extract value for interpreted kinds."
                                                  , "*** "
                                                  , "*** Only truly uninterpreted sorts should be used with 'getUninterpretedValue.'"
                                                  ]

-- | Get the value of a term, but in CW form. Used internally. The model-index, in particular is extremely Z3 specific!
getValueCWHelper :: Maybe Int -> SW -> Query CW
getValueCWHelper mbi s = do
       let nm  = show s
           k   = kindOf s

           modelIndex = case mbi of
                          Nothing -> ""
                          Just i  -> " :model_index " ++ show i

           cmd        = "(get-value (" ++ nm ++ ")" ++ modelIndex ++ ")"

           bad = unexpected "getModel" cmd ("a value binding for kind: " ++ show k) Nothing

           getUIIndex (KUserSort  _ (Right xs)) i = i `elemIndex` xs
           getUIIndex _                         _ = Nothing

       r <- ask cmd

       let isIntegral sw = isBoolean sw || isBounded sw || isInteger sw

           extract (ENum    i) | isIntegral      s = return $ mkConstCW  k (fst i)
           extract (EReal   i) | isReal          s = return $ CW KReal   (CWAlgReal i)
           extract (EFloat  i) | isFloat         s = return $ CW KFloat  (CWFloat   i)
           extract (EDouble i) | isDouble        s = return $ CW KDouble (CWDouble  i)
           extract (ECon    i) | isUninterpreted s = return $ CW k       (CWUserSort (getUIIndex k i, i))
           extract _                               = bad r Nothing

       parse r bad $ \case EApp [EApp [ECon v, val]] | v == nm -> extract val
                           _                                   -> bad r Nothing

-- | Get the value of a term. If the kind is Real and solver supports decimal approximations,
-- we will "squash" the representations.
getValueCW :: Maybe Int -> SW -> Query CW
getValueCW mbi s
  | kindOf s /= KReal
  = getValueCWHelper mbi s
  | True
  = do cfg <- getConfig
       if not (supportsApproxReals (capabilities (solver cfg)))
          then getValueCWHelper mbi s
          else do send True "(set-option :pp.decimal false)"
                  rep1 <- getValueCWHelper mbi s
                  send True   "(set-option :pp.decimal true)"
                  send True $ "(set-option :pp.decimal_precision " ++ show (printRealPrec cfg) ++ ")"
                  rep2 <- getValueCWHelper mbi s

                  let bad = unexpected "getValueCW" "get-value" ("a real-valued binding for " ++ show s) Nothing (show (rep1, rep2)) Nothing

                  case (rep1, rep2) of
                    (CW KReal (CWAlgReal a), CW KReal (CWAlgReal b)) -> return $ CW KReal (CWAlgReal (mergeAlgReals ("Cannot merge real-values for " ++ show s) a b))
                    _                                                -> bad

-- | Check for satisfiability.
checkSat :: Query CheckSatResult
checkSat = do cfg <- getConfig
              checkSatUsing $ satCmd cfg

-- | Check for satisfiability with a custom check-sat-using command.
checkSatUsing :: String -> Query CheckSatResult
checkSatUsing cmd = do let bad = unexpected "checkSat" cmd "one of sat/unsat/unknown" Nothing

                       r <- ask cmd

                       parse r bad $ \case ECon "sat"     -> return Sat
                                           ECon "unsat"   -> return Unsat
                                           ECon "unknown" -> return Unk
                                           _              -> bad r Nothing

-- | What are the top level inputs? Trackers are returned as top level existentials
getQuantifiedInputs :: Query [(Quantifier, NamedSymVar)]
getQuantifiedInputs = do State{rinps} <- get
                         (rQinps, rTrackers) <- liftIO $ readIORef rinps

                         let qinps    = reverse rQinps
                             trackers = map (EX,) $ reverse rTrackers

                             -- separate the existential prefix, which will go first
                             (preQs, postQs) = span (\(q, _) -> q == EX) qinps

                         return $ preQs ++ trackers ++ postQs

-- | Repeatedly issue check-sat, after refuting the previous model.
-- The bool is true if the model is unique upto prefix existentials.
getAllSatResult :: Query (Bool, Bool, [SMTResult])
getAllSatResult = do queryDebug ["*** Checking Satisfiability, all solutions.."]

                     cfg <- getConfig

                     State{rUsedKinds} <- get

                     ki    <- liftIO $ readIORef rUsedKinds
                     qinps <- getQuantifiedInputs

                     let usorts = [s | us@(KUserSort s _) <- Set.toList ki, isFree us]

                     unless (null usorts) $ queryDebug [ "*** SBV.allSat: Uninterpreted sorts present: " ++ unwords usorts
                                                       , "***             SBV will use equivalence classes to generate all-satisfying instances."
                                                       ]

                     let vars :: [(SVal, NamedSymVar)]
                         vars = let allModelInputs = takeWhile ((/= ALL) . fst) qinps

                                    sortByNodeId :: [NamedSymVar] -> [NamedSymVar]
                                    sortByNodeId = sortBy (compare `on` (\(SW _ n, _) -> n))

                                    mkSVal :: NamedSymVar -> (SVal, NamedSymVar)
                                    mkSVal nm@(sw, _) = (SVal (kindOf sw) (Right (cache (const (return sw)))), nm)

                                in map mkSVal $ sortByNodeId [nv | (_, nv@(_, n)) <- allModelInputs, not (isNonModelVar cfg n)]

                         -- If we have any universals, then the solutions are unique upto prefix existentials.
                         w = ALL `elem` map fst qinps

                     (sc, ms) <- loop vars cfg
                     return (sc, w, reverse ms)

   where isFree (KUserSort _ (Left _)) = True
         isFree _                      = False

         loop vars cfg = go (1::Int) []
            where go :: Int -> [SMTResult] -> Query (Bool, [SMTResult])
                  go !cnt sofar
                   | Just maxModels <- allSatMaxModelCount cfg, cnt > maxModels
                   = do queryDebug ["*** Maximum model count request of " ++ show maxModels ++ " reached, stopping the search."]
                        return (True, sofar)
                   | True
                   = do queryDebug ["Looking for solution " ++ show cnt]
                        cs <- checkSat
                        case cs of
                          Unsat -> return (False, sofar)
                          Unk   -> do queryDebug ["*** Solver returned unknown, terminating query."]
                                      return (False, sofar)
                          Sat   -> do assocs <- mapM (\(sval, (sw, n)) -> do cw <- getValueCW Nothing sw
                                                                             return (n, (sval, cw))) vars

                                      let m = Satisfiable cfg SMTModel { modelObjectives = []
                                                                       , modelAssocs     = [(n, cw) | (n, (_, cw)) <- assocs]
                                                                       }

                                          (interpreteds, uninterpreteds) = partition (not . isFree . kindOf . fst) (map snd assocs)

                                          -- For each "interpreted" variable, figure out the model equivalence
                                          -- NB. When the kind is floating, we *have* to be careful, since +/- zero, and NaN's
                                          -- and equality don't get along!
                                          interpretedEqs :: [SVal]
                                          interpretedEqs = [mkNotEq (kindOf sv) sv (SVal (kindOf sv) (Left cw)) | (sv, cw) <- interpreteds]
                                             where mkNotEq k a b
                                                    | isDouble k || isFloat k = svNot (a `fpNotEq` b)
                                                    | True                    = a `svNotEqual` b

                                                   fpNotEq a b = SVal KBool $ Right $ cache r
                                                       where r st = do swa <- svToSW st a
                                                                       swb <- svToSW st b
                                                                       newExpr st KBool (SBVApp (IEEEFP FP_ObjEqual) [swa, swb])

                                          -- For each "uninterpreted" variable, use equivalence class
                                          uninterpretedEqs :: [SVal]
                                          uninterpretedEqs = concatMap pwDistinct         -- Assert that they are pairwise distinct
                                                           . filter (\l -> length l > 1)  -- Only need this class if it has at least two members
                                                           . map (map fst)                -- throw away values, we only need svals
                                                           . groupBy ((==) `on` snd)      -- make sure they belong to the same sort and have the same value
                                                           . sortBy (comparing snd)       -- sort them according to their CW (i.e., sort/value)
                                                           $ uninterpreteds
                                            where pwDistinct :: [SVal] -> [SVal]
                                                  pwDistinct ss = [x `svNotEqual` y | (x:ys) <- tails ss, y <- ys]

                                          eqs = interpretedEqs ++ uninterpretedEqs
                                          disallow = case eqs of
                                                       [] -> Nothing
                                                       _  -> Just $ SBV $ foldr1 svOr eqs

                                      let resultsSoFar = m : sofar

                                      -- make sure there's some var. This happens! 'allSat true' is the pathetic example.

                                      case disallow of
                                        Nothing -> return (False, resultsSoFar)
                                        Just d  -> do constrain d
                                                      go (cnt+1) resultsSoFar

-- | Retrieve the set of unsatisfiable assumptions, following a call to 'checkSatAssumingWithUnsatisfiableSet'. Note that
-- this function isn't exported to the user, but rather used internally. The user simple calls 'checkSatAssumingWithUnsatisfiableSet'.
getUnsatAssumptions :: [String] -> [(String, a)] -> Query [a]
getUnsatAssumptions originals proxyMap = do
        let cmd = "(get-unsat-assumptions)"

            bad = unexpected "getUnsatAssumptions" cmd "a list of unsatisfiable assumptions"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       setOption $ ProduceUnsatAssumptions True"
                                  , ""
                                  , "to make sure the solver is ready for producing unsat assumptions,"
                                  , "and that there is a model by first issuing a 'checkSat' call."
                                  ]

            fromECon (ECon s) = Just s
            fromECon _        = Nothing

        r <- ask cmd

        -- If unsat-cores are enabled, z3 might end-up printing an assumption that wasn't
        -- in the original list of assumptions for `check-sat-assuming`. So, we walk over
        -- and ignore those that weren't in the original list, and put a warning for those
        -- we couldn't find.
        let walk []     sofar = return $ reverse sofar
            walk (a:as) sofar = case a `lookup` proxyMap of
                                  Just v  -> walk as (v:sofar)
                                  Nothing -> do queryDebug [ "*** In call to 'getUnsatAssumptions'"
                                                           , "***"
                                                           , "***    Unexpected assumption named: " ++ show a
                                                           , "***    Was expecting one of       : " ++ show originals
                                                           , "***"
                                                           , "*** This can happen if unsat-cores are also enabled. Ignoring."
                                                           ]
                                                walk as sofar

        parse r bad $ \case
           EApp es | Just xs <- mapM fromECon es -> walk xs []
           _                                     -> bad r Nothing

-- | Timeout a query action, typically a command call to the underlying SMT solver.
-- The duration is in microseconds (@1\/10^6@ seconds). If the duration
-- is negative, then no timeout is imposed. When specifying long timeouts, be careful not to exceed
-- @maxBound :: Int@. (On a 64 bit machine, this bound is practically infinite. But on a 32 bit
-- machine, it corresponds to about 36 minutes!)
--
-- Semantics: The call @timeout n q@ causes the timeout value to be applied to all interactive calls that take place
-- as we execute the query @q@. That is, each call that happens during the execution of @q@ gets a separate
-- time-out value, as opposed to one timeout value that limits the whole query. This is typically the intended behavior.
-- It is advisible to apply this combinator to calls that involve a single call to the solver for
-- finer control, as opposed to an entire set of interactions. However, different use cases might call for different scenarios.
--
-- If the solver responds within the time-out specified, then we continue as usual. However, if the backend solver times-out
-- using this mechanism, there is no telling what the state of the solver will be. Thus, we raise an error in this case.
timeout :: Int -> Query a -> Query a
timeout n q = do modifyQueryState (\qs -> qs {queryTimeOutValue = Just n})
                 r <- q
                 modifyQueryState (\qs -> qs {queryTimeOutValue = Nothing})
                 return r

-- | Bail out if a parse goes bad
parse :: String -> (String -> Maybe [String] -> a) -> (SExpr -> a) -> a
parse r fCont sCont = case parseSExpr r of
                        Left  e   -> fCont r (Just [e])
                        Right res -> sCont res

-- | Bail out if we don't get what we expected
unexpected :: String -> String -> String -> Maybe [String] -> String -> Maybe [String] -> Query a
unexpected ctx sent expected mbHint received mbReason = do
        -- empty the response channel first
        extras <- retrieveResponse "terminating upon unexpected response" (Just 5000000)

        error $ unlines $ [ ""
                          , "*** Data.SBV: Unexpected response from the solver."
                          , "***    Context : " `alignDiagnostic` ctx
                          , "***    Sent    : " `alignDiagnostic` sent
                          , "***    Expected: " `alignDiagnostic` expected
                          , "***    Received: " `alignDiagnostic` unlines (received : extras)
                          ]
                       ++ [ "***    Reason  : " `alignDiagnostic` unlines r | Just r <- [mbReason]]
                       ++ [ "***    Hint    : " `alignDiagnostic` unlines r | Just r <- [mbHint]]

-- | Convert a query result to an SMT Problem
runProofOn :: SMTConfig -> Bool -> [String] -> Result -> SMTProblem
runProofOn config isSat comments res@(Result ki _qcInfo _codeSegs is consts tbls arrs uis axs pgm cstrs _assertions outputs) =
     let flipQ (ALL, x) = (EX,  x)
         flipQ (EX,  x) = (ALL, x)

         skolemize :: [(Quantifier, NamedSymVar)] -> [Either SW (SW, [SW])]
         skolemize quants = go quants ([], [])
           where go []                   (_,  sofar) = reverse sofar
                 go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                 go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)

         qinps      = if isSat then fst is else map flipQ (fst is)
         skolemMap  = skolemize qinps

         o = case outputs of
               []  -> trueSW
               [so] -> case so of
                        SW KBool _ -> so
                        _          -> trueSW
                                      {-
                                      -- TODO: We used to error out here, but "safeWith" might have a non-bool out
                                      -- I wish we can get rid of this and still check for it. Perhaps this entire
                                      -- runProofOn might disappear.
                                      error $ unlines [ "Impossible happened, non-boolean output: " ++ show so
                                                      , "Detected while generating the trace:\n" ++ show res
                                                      ]
                                      -}
               os  -> error $ unlines [ "User error: Multiple output values detected: " ++ show os
                                      , "Detected while generating the trace:\n" ++ show res
                                      , "*** Check calls to \"output\", they are typically not needed!"
                                      ]

     in SMTProblem { smtLibPgm = toSMTLib config ki isSat comments is skolemMap consts tbls arrs uis axs pgm cstrs o }

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
