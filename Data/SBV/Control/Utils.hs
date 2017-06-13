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
     , ask, send, getValue, getModel, getUnsatAssumptions
     , ignoreExitCode
     , inNewContext
     , parse
     , unexpected
     , timeout
     , queryDebug
     , retrieveString
     ) where

import Data.List  (sortBy, intercalate)
import Data.Maybe (isNothing)

import Data.Int
import Data.Word

import qualified Data.Map as Map

import Control.Monad (when)
import Control.Monad.State.Lazy (get, modify', liftIO)

import Data.IORef (readIORef)

import Data.SBV.Core.Data     (SBV, AlgReal, sbvToSW)
import Data.SBV.Core.Symbolic ( SMTConfig(..), State, IncState(..), Query
                              , QueryContext(..), QueryState(..), withNewIncState, SMTResult(..)
                              )

import Data.SBV.SMT.SMTLib  (toIncSMTLib)
import Data.SBV.SMT.Utils   (showTimeoutValue)

import Data.SBV.Utils.SExpr

-- | Get the current configuration
getConfig :: Query SMTConfig
getConfig = queryConfig <$> get

-- | Should we ignore the exit code from the solver upon finish?
-- The default is /not/ to ignore. However, you might want to set
-- this to 'False' before you issue a call to 'sbvResume', in case the interactive
-- part of your query caused solver to issue some errors that you would
-- like to ignore.
ignoreExitCode :: Bool -> Query ()
ignoreExitCode b = modify' (\qs -> qs {queryIgnoreExitCode  = b})

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
                       as    <- readIORef (rNewAsgns  is)
                       return $ toIncSMTLib cfg cnsts as cfg
        mapM_ (send True) ls

-- | Execute in a new incremental context
inNewContext :: (State -> IO a) -> Query a
inNewContext act = do QueryState{queryContext} <- get
                      (is, r) <- io $ withNewIncState (contextState queryContext) act
                      syncUpSolver is
                      return r

-- | Internal diagnostic messages.
queryDebug :: [String] -> Query ()
queryDebug msg = do QueryState{queryConfig} <- get
                    when (verbose queryConfig) $ mapM_ (io . putStrLn) msg

-- | Send a string to the solver, and return the response
ask :: String -> Query String
ask s = do QueryState{queryAsk, queryTimeOutValue} <- get

           case queryTimeOutValue of
             Nothing -> queryDebug ["[SENDING]  " ++ s]
             Just i  -> queryDebug ["[SENDING, TimeOut: " ++ showTimeoutValue i ++ "]  " ++ s]
           r <- io $ queryAsk queryTimeOutValue s
           queryDebug ["[RECEIVED] " ++ r]

           return r

-- | Send a string to the solver. If the first argument is 'True', we will require
-- a "success" response as well. Otherwise, we'll fire and forget.
send :: Bool -> String -> Query ()
send requireSuccess s = do

            QueryState{queryAsk, querySend, queryConfig, queryTimeOutValue} <- get

            if requireSuccess
               then do r <- io $ queryAsk queryTimeOutValue s

                       case words r of
                         ["success"] -> when (verbose queryConfig) $ io $ putStrLn $ "[SUCCESS] " ++ s
                         _           -> do case queryTimeOutValue of
                                             Nothing -> io $ putStrLn $ "[FAILED]  " ++ s
                                             Just i  -> io $ putStrLn $ "[FAILED, TimeOut: " ++ showTimeoutValue i ++ "]  " ++ s
                                           unexpected "Command" s "success" Nothing r Nothing

               else io $ querySend queryTimeOutValue s  -- fire and forget. if you use this, you're on your own!

-- | Retrieve string from the solver. Should only be used for internal purposes. Use 'send'/'ask'. If the time-out
-- is given and and is exceeded by the solver, then we will raise an error.
retrieveString :: Maybe Int -> Query String
retrieveString mbTo = do QueryState{queryRetrieveString} <- get
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

-- | Get the value of free inputs, packing it into an SMTResult
getModel :: Query SMTResult
getModel = do QueryState{queryGetModel} <- get
              ms <- io queryGetModel
              case ms of
                [m] -> return m
                []  -> error   "Data.SBV: getModel: No models returned"
                _   -> error $ "Data.SBV: getModel: Expected one model, received: " ++ show (length ms)

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
timeout n q = do modify' (\qs -> qs {queryTimeOutValue = Just n})
                 r <- q
                 modify' (\qs -> qs {queryTimeOutValue = Nothing})
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
