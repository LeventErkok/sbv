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
     , ask, send, getValue, getModel
     , ignoreExitCode
     , inNewContext
     , parse
     , unexpected
     ) where

import Data.List (sortBy)
import Data.Int
import Data.Word

import qualified Data.Map as Map

import Control.Monad.State.Lazy (get, modify', liftIO)

import Data.IORef (readIORef)

import Data.SBV.Core.Data     (SBV, AlgReal, sbvToSW)
import Data.SBV.Core.Symbolic (SMTConfig(..), State, IncState(..), Query, QueryContext(..), QueryState(..), withNewIncState, SMTResult(..))

import Data.SBV.SMT.SMTLib  (toIncSMTLib)

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
        mapM_ send ls

-- | Execute in a new incremental context
inNewContext :: (State -> IO a) -> Query a
inNewContext act = do QueryState{queryContext} <- get
                      (is, r) <- io $ withNewIncState (contextState queryContext) act
                      syncUpSolver is
                      return r

-- | Send a string to the solver, and return the response
ask :: String -> Query String
ask s = do QueryState{queryAsk, queryConfig} <- get

           let dbg what m
                 | verbose queryConfig = io . putStrLn $ what ++ " " ++ m
                 | True                = return ()

           dbg "-->" s
           r <- io $ queryAsk s
           dbg "<--" r

           return r

-- | Send a string to the solver, where no answer is expected
send :: String -> Query ()
send s = do QueryState{querySend, queryConfig} <- get

            let dbg what m
                  | verbose queryConfig = io . putStrLn $ what ++ " " ++ m
                  | True                = return ()

            dbg "-->" s
            io $ querySend s

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
                    bad = unexpected "getValue" cmd "a model value"
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

-- | Bail out if a parse goes bad
parse :: String -> (String -> Maybe String -> a) -> (SExpr -> a) -> a
parse r fCont sCont = case parseSExpr r of
                        Left  e   -> fCont r (Just e)
                        Right res -> sCont res

-- | Bail out if we don't get what we expected
unexpected :: String -> String -> String -> String -> Maybe String -> a
unexpected ctx sent expected received mbReason = error $ unlines $ [
          ""
        , "*** Data.SBV: Unexpected response from the solver."
        , "***    Context : " ++ ctx
        , "***    Sent    : " ++ sent
        , "***    Expected: " ++ expected
        , "***    Received: " ++ received
        ]
     ++ [ "***    Reason  : " ++ r | Just r <- [mbReason]]
