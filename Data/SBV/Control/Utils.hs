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

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Data.SBV.Control.Utils (
       io
     , ask, send, getValue, getValueCW, getUnsatAssumptions
     , getQueryState, modifyQueryState, getConfig, getObjectives, getQuantifiedInputs
     , checkSat, checkSatUsing, getAllSatResult
     , inNewContext
     , parse
     , unexpected
     , timeout
     , queryDebug
     , retrieveResponse
     ) where

import Data.List  (sortBy, intercalate, elemIndex, partition, groupBy, tails)
import Data.Maybe (isNothing)

import Data.Ord      (comparing)
import Data.Function (on)

import Data.Int
import Data.Word

import qualified Data.Map as Map

import Control.Monad            (when, unless)
import Control.Monad.State.Lazy (get, liftIO)

import Data.IORef (readIORef, writeIORef)

import Data.SBV.Core.Data     ( SW(..), CW(..), SBV, AlgReal, sbvToSW, kindOf, Kind(..)
                              , HasKind(..), mkConstCW, CWVal(..), SMTResult(..)
                              , NamedSymVar, SMTConfig(..), Query, SMTModel(..)
                              , QueryState(..), SVal(..), Quantifier(..), cache
                              , newExpr, SBVExpr(..), Op(..), FPOp(..), SBV(..)
                              , SolverContext(..), SBool, Objective(..)
                              )
import Data.SBV.Core.Symbolic (IncState(..), withNewIncState, State(..), svToSW, registerLabel)

import Data.SBV.Core.Operations (svNot, svNotEqual, svOr)

import Data.SBV.SMT.SMTLib  (toIncSMTLib)
import Data.SBV.SMT.Utils   (showTimeoutValue, annotateWithName)

import Data.SBV.Utils.SExpr
import Data.SBV.Control.Types

import qualified Data.Set as Set (toList)

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

-- | Perform an arbitrary IO action.
io :: IO a -> Query a
io = liftIO

-- | Sync-up the external solver with new context we have generated
syncUpSolver :: IncState -> Query ()
syncUpSolver is = do
        cfg <- getConfig
        ls  <- io $ do let swapc ((_, a), b)   = (b, a)
                           cmp   (a, _) (b, _) = a `compare` b
                       cnsts <- (sortBy cmp . map swapc . Map.toList) `fmap` readIORef (rNewConsts is)
                       as    <- readIORef (rNewAsgns is)
                       return $ toIncSMTLib cfg cnsts as cfg
        mapM_ (send True) ls

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

-- | Internal diagnostic messages.
queryDebug :: [String] -> Query ()
queryDebug msg = do QueryState{queryConfig} <- getQueryState
                    when (verbose queryConfig) $ mapM_ (io . putStrLn) msg

-- | Send a string to the solver, and return the response
ask :: String -> Query String
ask s = do QueryState{queryAsk, queryTimeOutValue} <- getQueryState

           case queryTimeOutValue of
             Nothing -> queryDebug ["[SEND] " ++ s]
             Just i  -> queryDebug ["[SEND, TimeOut: " ++ showTimeoutValue i ++ "] " ++ s]
           r <- io $ queryAsk queryTimeOutValue s
           queryDebug ["[RECV] " ++ r]

           return r

-- | Send a string to the solver. If the first argument is 'True', we will require
-- a "success" response as well. Otherwise, we'll fire and forget.
send :: Bool -> String -> Query ()
send requireSuccess s = do

            QueryState{queryAsk, querySend, queryConfig, queryTimeOutValue} <- getQueryState

            if requireSuccess
               then do r <- io $ queryAsk queryTimeOutValue s

                       let align tag multi = intercalate "\n" $ zipWith (++) (tag : repeat (replicate (length tag) ' ')) (filter (not . null) (lines multi))

                       case words r of
                         ["success"] -> when (verbose queryConfig) $ io $ putStrLn $ align "[GOOD] " s
                         _           -> do case queryTimeOutValue of
                                             Nothing -> io $ putStrLn $ align "[FAIL] " s
                                             Just i  -> io $ putStrLn $ align ("[FAIL, TimeOut: " ++ showTimeoutValue i ++ "]  ") s
                                           unexpected "Command" s "success" Nothing r Nothing

               else io $ querySend queryTimeOutValue s  -- fire and forget. if you use this, you're on your own!

-- | Retrieve a response from the solver, that is a valid s-expression. Should only
-- be used for internal purposes. Use 'send'/'ask'. If the time-out
-- is given and and is exceeded by the solver, then we will raise an error.
retrieveResponse :: Maybe Int -> Query String
retrieveResponse mbTo = do QueryState{queryRetrieveResponse, queryConfig} <- getQueryState
                           s <- io $ queryRetrieveResponse mbTo
                           when (verbose queryConfig) $ io $ do
                                let align tag multi = intercalate "\n" $ zipWith (++) (tag : repeat (replicate (length tag) ' ')) (filter (not . null) (lines multi))
                                putStrLn $ align "[RECV] " s
                           return s

-- | A class which allows for sexpr-conversion to values
class SMTValue a where
  sexprToVal :: SExpr -> Maybe a

  default sexprToVal :: Integral a => SExpr -> Maybe a
  sexprToVal (ENum (i, _)) = Just $ fromIntegral i
  sexprToVal _             = Nothing

instance SMTValue Int8
instance SMTValue Int16
instance SMTValue Int32
instance SMTValue Int64
instance SMTValue Word8
instance SMTValue Word16
instance SMTValue Word32
instance SMTValue Word64
instance SMTValue Integer

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

-- | Get the value of a term, but in CW form. Used internally. The model-index, in particular
-- is extremely Z3 specific!
getValueCW :: Maybe Int -> SW -> Query CW
getValueCW mbi s = do let nm  = show s
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

-- | What are the top level inputs?
getQuantifiedInputs :: Query [(Quantifier, NamedSymVar)]
getQuantifiedInputs = do State{rinps} <- get
                         liftIO $ reverse <$> readIORef rinps

-- | Repeatedly issue check-sat, after refuting the previous model.
-- The bool is true if the model is unique upto prefix existentials.
getAllSatResult :: Query (Bool, [SMTResult])
getAllSatResult = do queryDebug ["Checking Satisfiability, all solutions.."]

                     cfg <- getConfig

                     State{rUsedKinds} <- get

                     ki    <- liftIO $ readIORef rUsedKinds
                     qinps <- getQuantifiedInputs

                     let usorts = [s | us@(KUserSort s _) <- Set.toList ki, isFree us]

                     unless (null usorts) $ queryDebug [ "SBV.allSat: Uninterpreted sorts present: " ++ unwords usorts
                                                       , "            SBV will use equivalence classes to generate all-satisfying instances."
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

                     ms <- loop vars cfg
                     return (w, ms)

   where isFree (KUserSort _ (Left _)) = True
         isFree _                      = False

         loop vars cfg = go (1::Int)
            where go :: Int -> Query [SMTResult]
                  go cnt = do queryDebug ["Looking for solution " ++ show cnt]
                              cs <- checkSat
                              case cs of
                                Unsat -> return []
                                Unk   -> do queryDebug ["Solver returned unknown, terminating query."]
                                            return []
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

                                            -- make sure there's some var. This happens! 'allSat true' is the pathetic example.
                                            case disallow of
                                              Nothing -> return [m]
                                              Just d  -> do constrain d
                                                            rest <- go (cnt+1)
                                                            return $ m : rest

-- | Retrieve the set of unsatisfiable assumptions, following a call to 'checkSatAssuming'. Note that
-- this function isn't exported to the user, but rather used internally. The user simple calls 'checkSatAssuming'.
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
unexpected :: String -> String -> String -> Maybe [String] -> String -> Maybe [String] -> a
unexpected ctx sent expected mbHint received mbReason = error $ unlines $ [
          ""
        , "*** Data.SBV: Unexpected response from the solver."
        , "***    Context : " ++ ctx
        , "***    Sent    : " ++ sent
        , "***    Expected: " ++ expected
        ]
     ++ [ "***    Received: " ++ received          | isNothing mbReason  ]
     ++ [ "***    Reason  : " ++ intercalate tab r | Just r <- [mbReason]]
     ++ [ "***    Hint    : " ++ intercalate tab r | Just r <- [mbHint]]
 where tab = "\n***              "
