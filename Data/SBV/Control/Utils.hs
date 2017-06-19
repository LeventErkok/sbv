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

{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NamedFieldPuns    #-}

module Data.SBV.Control.Utils (
       io
     , ask, send, getValue, getValueCW, getUnsatAssumptions
     , getQueryState, modifyQueryState, getConfig
     , inNewContext
     , parse
     , unexpected
     , timeout
     , queryDebug
     , retrieveString
     ) where

import Data.List  (sortBy, intercalate, elemIndex)
import Data.Maybe (isNothing)

import Data.Int
import Data.Word

import qualified Data.Map as Map

import Control.Monad (when)
import Control.Monad.State.Lazy (get, liftIO)

import Data.IORef (readIORef, writeIORef)

import Data.SBV.Core.Data     (SW(..), CW(..), SBV, AlgReal, sbvToSW, kindOf, Kind(..), HasKind(..), mkConstCW, CWVal(..))
import Data.SBV.Core.Symbolic ( SMTConfig(..), State(..), IncState(..), Query
                              , QueryState(..), withNewIncState
                              )

import Data.SBV.SMT.SMTLib  (toIncSMTLib)
import Data.SBV.SMT.Utils   (showTimeoutValue)

import Data.SBV.Utils.SExpr

-- | Get the current configuration
getConfig :: Query SMTConfig
getConfig = queryConfig <$> getQueryState

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
                                             Nothing -> io $ putStrLn $ align "[FAIL]  " s
                                             Just i  -> io $ putStrLn $ align ("[FAIL, TimeOut: " ++ showTimeoutValue i ++ "]  ") s
                                           unexpected "Command" s "success" Nothing r Nothing

               else io $ querySend queryTimeOutValue s  -- fire and forget. if you use this, you're on your own!

-- | Retrieve string from the solver. Should only be used for internal purposes. Use 'send'/'ask'. If the time-out
-- is given and and is exceeded by the solver, then we will raise an error.
retrieveString :: Maybe Int -> Query String
retrieveString mbTo = do QueryState{queryRetrieveString} <- getQueryState
                         io $ queryRetrieveString mbTo

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

-- | Get the value of a term, but in CW form. Used internally.
getValueCW :: SW -> Query CW
getValueCW s = do let nm  = show s
                      cmd = "(get-value (" ++ nm ++ "))"
                      k   = kindOf s

                      bad = unexpected "getModel" cmd ("a value binding for kind: " ++ show k) Nothing

                      getUIIndex (KUserSort  _ (Right xs)) i = i `elemIndex` xs
                      getUIIndex _                         _ = Nothing

                  r <- ask cmd

                  let extract (ENum    i) | isBoolean       s || isBounded s = return $ mkConstCW  k (fst i)
                      extract (EReal   i) | isReal          s                = return $ CW KReal   (CWAlgReal i)
                      extract (EDouble i) | isDouble        s                = return $ CW KDouble (CWDouble  i)
                      extract (EFloat  i) | isFloat         s                = return $ CW KFloat  (CWFloat   i)
                      extract (ECon    i) | isUninterpreted s                = return $ CW k       (CWUserSort (getUIIndex k i, i))
                      extract _                                              = bad r Nothing

                  parse r bad $ \case EApp [EApp [ECon v, val]] | v == nm -> extract val
                                      _                                   -> bad r Nothing

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
parse :: String -> (String -> Maybe String -> a) -> (SExpr -> a) -> a
parse r fCont sCont = case parseSExpr r of
                        Left  e   -> fCont r (Just e)
                        Right res -> sCont res

-- | Bail out if we don't get what we expected
unexpected :: String -> String -> String -> Maybe [String] -> String -> Maybe String -> a
unexpected ctx sent expected mbHint received mbReason = error $ unlines $ [
          ""
        , "*** Data.SBV: Unexpected response from the solver."
        , "***    Context : " ++ ctx
        , "***    Sent    : " ++ sent
        , "***    Expected: " ++ expected
        ]
     ++ [ "***    Received: " ++ received          | isNothing mbReason  ]
     ++ [ "***    Reason  : " ++ r                 | Just r <- [mbReason]]
     ++ [ "***    Hint    : " ++ intercalate tab r | Just r <- [mbHint]]
 where tab = "\n***              "
