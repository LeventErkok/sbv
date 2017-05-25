-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Control sublanguage for interacting with SMT solvers.
-----------------------------------------------------------------------------

{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}

module Data.SBV.Control(
     -- * Add new assertions
       assert

     -- * Sending an arbitrary string
     , send, ask

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat

     -- * Extracting a value
     , getValue

     -- * Controlling the solver behavior
     , SMTOption(..), setOption
     , ignoreExitCode

     -- * Terminating the query
     , sbvResume
     , result
     , failure

     -- * Performing actions
     , io
     ) where

import Control.Monad.State.Lazy (get, modify)
import Control.Monad.Trans      (liftIO)

import Data.IORef (readIORef)
import Data.List  (sortBy)

import qualified Data.Map as Map (toList)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (QueryState(..), Query(..), SMTResult(..), SMTConfig(..), withNewIncState, IncState(..))

import Data.SBV.SMT.SMTLib (toIncSMTLib2)

import Data.SBV.Provers.SExpr

import Data.Int
import Data.Word

-- | Get the current configuration
getConfig :: Query SMTConfig
getConfig = queryConfig <$> get

-- | Get the current context
getContextState :: Query State
getContextState = contextState . queryContext <$> get

-- | Should we ignore the exit code from the solver upon finish?
-- The default is /not/ to ignore. However, you might want to set
-- this to 'False' before you issue a call to 'sbvResume', in case the interactive
-- part of your query caused solver to issue some errors that you would
-- like to ignore.
ignoreExitCode :: Bool -> Query ()
ignoreExitCode b = modify (\qs -> qs {queryIgnoreExitCode  = b})

-- | Send a string to the solver, and return the response
ask :: String -> Query String
ask s = do QueryState{queryAsk, queryConfig} <- get

           let dbg what m
                 | verbose queryConfig = message $ what ++ " " ++ m
                 | True                = return ()

           dbg "-->" s
           r <- io $ queryAsk s
           dbg "<--" r

           return r

-- | Send a string to the solver, where no answer is expected
send :: String -> Query ()
send s = do QueryState{querySend, queryConfig} <- get

            let dbg what m
                  | verbose queryConfig = message $ what ++ " " ++ m
                  | True                = return ()

            dbg "-->" s
            io $ querySend s

-- | Perform an arbitrary IO action.
io :: IO a -> Query a
io = liftIO

-- | Print a message on the console
message :: String -> Query ()
message = io . putStrLn

-- | Run what SBV would've run, should we not have taken control. Note that
-- if you call this function, SBV will issue a call to check-sat and then
-- collect the model with respect to all the changes the query has performed.
-- If you already do have a model built during the query, use 'result' to
-- return it, instead of telling sbv to do it on its own.
sbvResume :: Query [SMTResult]
sbvResume = do QueryState{queryDefault, queryIgnoreExitCode} <- get
               io $ queryDefault queryIgnoreExitCode

-- | Sync-up the external solver with new context we have generated
syncUpSolver :: IncState -> Query ()
syncUpSolver is = do
        cfg <- getConfig
        ls  <- io $ do let swapc ((_, a), b)   = (b, a)
                           cmp   (a, _) (b, _) = a `compare` b
                       cnsts <- (sortBy cmp . map swapc . Map.toList) `fmap` readIORef (rNewConsts is)
                       as    <- readIORef (rNewAsgns  is)
                       return $ toIncSMTLib2 cnsts as cfg
        mapM_ send ls

-- | Execute in a new incremental context
inNewContext :: (State -> IO a) -> Query a
inNewContext act = do st <- getContextState
                      (is, r) <- io $ withNewIncState st act
                      syncUpSolver is
                      return r

-- | Option values that can be set in the solver. Note that not
-- all solvers may support all of these!
data SMTOption = DiagnosticOutputChannel FilePath

-- | Show instance for SMTOption maintains smt-lib format per the
-- SMTLib2 standard document
instance Show SMTOption where
   show (DiagnosticOutputChannel f) = ":diagnostic-output-channel " ++ show f

-- | Set an option
setOption :: SMTOption -> Query ()
setOption o = send $ "(set-option " ++ show o ++ ")"

-- | Assert a new "fact"
assert :: SBool -> Query ()
assert s = do sw <- inNewContext (`sbvToSW` s)
              send $ "(assert " ++ show sw ++ ")"

-- | Result of a 'checkSat' call.
data CheckSatResult = Sat | Unsat | Unk
                    deriving (Eq, Show)

-- | Check for satisfiability.
checkSat :: Query CheckSatResult
checkSat = do let cmd = "(check-sat)"
                  bad = unexpected "checkSat" cmd "one of sat/unsat/unknown"
              r <- ask cmd
              parse r bad $ \case ECon "sat"     -> return Sat
                                  ECon "unsat"   -> return Unsat
                                  ECon "unknown" -> return Unk
                                  _              -> bad r Nothing

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

-- | Produce this answer as the result
result :: SMTResult -> Query [SMTResult]
result x = return [x]

-- | Fail with error
failure :: [String] -> Query [SMTResult]
failure ms = do QueryState{queryConfig} <- get
                result $ ProofError queryConfig ms

{- $commIntro
Some good text here
-}
