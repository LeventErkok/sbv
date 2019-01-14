-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Control.Utils
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Query related utils.
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeSynonymInstances  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.SBV.Control.Utils (
       io
     , ask, send, getValue, getUninterpretedValue, getValueCV, getUnsatAssumptions, SMTValue(..)
     , getQueryState, modifyQueryState, getConfig, getObjectives, getSBVAssertions, getSBVPgm, getQuantifiedInputs, getObservables
     , checkSat, checkSatUsing, getAllSatResult
     , inNewContext, freshVar, freshVar_, freshArray, freshArray_
     , parse
     , unexpected
     , timeout
     , queryDebug
     , retrieveResponse
     , recoverKindedValue
     , runProofOn
     , executeQuery
     ) where

import Data.Maybe (isJust)
import Data.List  (sortBy, sortOn, elemIndex, partition, groupBy, tails, intercalate)

import Data.Char     (isPunctuation, isSpace, chr, ord, isDigit)
import Data.Function (on)

import Data.Proxy
import Data.Typeable (Typeable)

import Data.Int
import Data.Word

import qualified Data.Map.Strict    as Map
import qualified Data.IntMap.Strict as IMap

import Control.Monad            (join, unless)
import Control.Monad.IO.Class   (MonadIO, liftIO)
import Control.Monad.Trans      (lift)
import Control.Monad.Reader     (runReaderT)

import Data.IORef (readIORef, writeIORef)

import Data.Time (getZonedTime)

import Data.SBV.Core.Data     ( SV(..), trueSV, falseSV, CV(..), trueCV, falseCV, SBV, AlgReal, sbvToSV, kindOf, Kind(..)
                              , HasKind(..), mkConstCV, CVal(..), SMTResult(..)
                              , NamedSymVar, SMTConfig(..), SMTModel(..)
                              , QueryState(..), SVal(..), Quantifier(..), cache
                              , newExpr, SBVExpr(..), Op(..), FPOp(..), SBV(..), SymArray(..)
                              , SolverContext(..), SBool, Objective(..), SolverCapabilities(..), capabilities
                              , Result(..), SMTProblem(..), trueSV, SymVal(..), SBVPgm(..), SMTSolver(..), SBVRunMode(..)
                              )

import Data.SBV.Core.Symbolic ( IncState(..), withNewIncState, State(..), svToSV, symbolicEnv, SymbolicT
                              , MonadQuery(..), QueryContext(..), Queriable(..)
                              , registerLabel, svMkSymVar
                              , isSafetyCheckingIStage, isSetupIStage, isRunIStage, IStage(..), QueryT(..)
                              , extractSymbolicSimulationState
                              )

import Data.SBV.Core.AlgReals   (mergeAlgReals)
import Data.SBV.Core.Operations (svNot, svNotEqual, svOr)

import Data.SBV.SMT.SMTLib  (toIncSMTLib, toSMTLib)
import Data.SBV.SMT.Utils   (showTimeoutValue, addAnnotations, alignPlain, debug, mergeSExpr, SBVException(..))

import Data.SBV.Utils.ExtractIO
import Data.SBV.Utils.Lib (qfsToString, isKString)
import Data.SBV.Utils.SExpr
import Data.SBV.Control.Types

import qualified Data.Set as Set (toList)

import qualified Control.Exception as C

import GHC.Stack

import Unsafe.Coerce (unsafeCoerce) -- Only used safely!

-- | 'Data.SBV.Trans.Control.QueryT' as a 'SolverContext'.
instance MonadIO m => SolverContext (QueryT m) where
   constrain              = addQueryConstraint False []
   softConstrain          = addQueryConstraint True  []
   namedConstraint nm     = addQueryConstraint False [(":named", nm)]
   constrainWithAttribute = addQueryConstraint False

   setOption o
     | isStartModeOption o = error $ unlines [ ""
                                             , "*** Data.SBV: '" ++ show o ++ "' can only be set at start-up time."
                                             , "*** Hint: Move the call to 'setOption' before the query."
                                             ]
     | True                = send True $ setSMTOption o

-- | Adding a constraint, possibly with attributes and possibly soft. Only used internally.
-- Use 'constrain' and 'namedConstraint' from user programs.
addQueryConstraint :: (MonadIO m, MonadQuery m) => Bool -> [(String, String)] -> SBool -> m ()
addQueryConstraint isSoft atts b = do sv <- inNewContext (\st -> liftIO $ do mapM_ (registerLabel "Constraint" st) [nm | (":named", nm) <- atts]
                                                                             sbvToSV st b)

                                      unless (null atts && sv == trueSV) $
                                             send True $ "(" ++ asrt ++ " " ++ addAnnotations atts (show sv)  ++ ")"
   where asrt | isSoft = "assert-soft"
              | True   = "assert"

-- | Get the current configuration
getConfig :: (MonadIO m, MonadQuery m) => m SMTConfig
getConfig = queryConfig <$> getQueryState

-- | Get the objectives
getObjectives :: (MonadIO m, MonadQuery m) => m [Objective (SV, SV)]
getObjectives = do State{rOptGoals} <- queryState
                   io $ reverse <$> readIORef rOptGoals

-- | Get the program
getSBVPgm :: (MonadIO m, MonadQuery m) => m SBVPgm
getSBVPgm = do State{spgm} <- queryState
               io $ readIORef spgm

-- | Get the assertions put in via 'Data.SBV.sAssert'
getSBVAssertions :: (MonadIO m, MonadQuery m) => m [(String, Maybe CallStack, SV)]
getSBVAssertions = do State{rAsserts} <- queryState
                      io $ reverse <$> readIORef rAsserts

-- | Generalization of 'Data.SBV.Control.io'
io :: MonadIO m => IO a -> m a
io = liftIO

-- | Sync-up the external solver with new context we have generated
syncUpSolver :: (MonadIO m, MonadQuery m) => Bool -> IncState -> m ()
syncUpSolver afterAPush is = do
        cfg <- getConfig
        ls  <- io $ do let swap  (a, b)        = (b, a)
                           cmp   (a, _) (b, _) = a `compare` b
                           arrange (i, (at, rt, es)) = ((i, at, rt), es)
                       inps  <- reverse <$> readIORef (rNewInps is)
                       ks    <- readIORef (rNewKinds is)
                       cnsts <- sortBy cmp . map swap . Map.toList <$> readIORef (rNewConsts is)
                       arrs  <- IMap.toAscList <$> readIORef (rNewArrs is)
                       tbls  <- map arrange . sortBy cmp . map swap . Map.toList <$> readIORef (rNewTbls is)
                       uis   <- Map.toAscList <$> readIORef (rNewUIs is)
                       as    <- readIORef (rNewAsgns is)

                       return $ toIncSMTLib afterAPush cfg inps ks cnsts arrs tbls uis as cfg
        mapM_ (send True) $ mergeSExpr ls

-- | Retrieve the query context
getQueryState :: (MonadIO m, MonadQuery m) => m QueryState
getQueryState = do state <- queryState
                   mbQS  <- io $ readIORef (rQueryState state)
                   case mbQS of
                     Nothing -> error $ unlines [ ""
                                                , "*** Data.SBV: Impossible happened: Query context required in a non-query mode."
                                                , "Please report this as a bug!"
                                                ]
                     Just qs -> return qs

-- | Generalization of 'Data.SBV.Control.modifyQueryState'
modifyQueryState :: (MonadIO m, MonadQuery m) => (QueryState -> QueryState) -> m ()
modifyQueryState f = do state <- queryState
                        mbQS  <- io $ readIORef (rQueryState state)
                        case mbQS of
                          Nothing -> error $ unlines [ ""
                                                     , "*** Data.SBV: Impossible happened: Query context required in a non-query mode."
                                                     , "Please report this as a bug!"
                                                     ]
                          Just qs -> let fqs = f qs
                                     in fqs `seq` io $ writeIORef (rQueryState state) $ Just fqs

-- | Generalization of 'Data.SBV.Control.inNewContext'
inNewContext :: (MonadIO m, MonadQuery m) => (State -> IO a) -> m a
inNewContext act = do st <- queryState
                      (is, r) <- io $ withNewIncState st act
                      mbQS <- io . readIORef . rQueryState $ st
                      let afterAPush = case mbQS of
                                         Nothing -> False
                                         Just qs -> isJust (queryTblArrPreserveIndex qs)
                      syncUpSolver afterAPush is
                      return r

-- | Generic 'Queriable' instance for 'SymVal'/'SMTValue' values
instance (MonadIO m, SymVal a, SMTValue a) => Queriable m (SBV a) a where
  fresh   = freshVar_
  extract = getValue

-- | Generalization of 'Data.SBV.Control.freshVar_'
freshVar_ :: forall a m. (MonadIO m, MonadQuery m, SymVal a) => m (SBV a)
freshVar_ = inNewContext $ fmap SBV . svMkSymVar (Just EX) k Nothing
  where k = kindOf (Proxy @a)

-- | Generalization of 'Data.SBV.Control.freshVar'
freshVar :: forall a m. (MonadIO m, MonadQuery m, SymVal a) => String -> m (SBV a)
freshVar nm = inNewContext $ fmap SBV . svMkSymVar (Just EX) k (Just nm)
  where k = kindOf (Proxy @a)

-- | Generalization of 'Data.SBV.Control.freshArray_'
freshArray_ :: (MonadIO m, MonadQuery m, SymArray array, HasKind a, HasKind b) => Maybe (SBV b) -> m (array a b)
freshArray_ = mkFreshArray Nothing

-- | Generalization of 'Data.SBV.Control.freshArray'
freshArray :: (MonadIO m, MonadQuery m, SymArray array, HasKind a, HasKind b) => String -> Maybe (SBV b) -> m (array a b)
freshArray nm = mkFreshArray (Just nm)

-- | Creating arrays, internal use only.
mkFreshArray :: (MonadIO m, MonadQuery m, SymArray array, HasKind a, HasKind b) => Maybe String -> Maybe (SBV b) -> m (array a b)
mkFreshArray mbNm mbVal = inNewContext $ newArrayInState mbNm mbVal

-- | Generalization of 'Data.SBV.Control.queryDebug'
queryDebug :: (MonadIO m, MonadQuery m) => [String] -> m ()
queryDebug msgs = do QueryState{queryConfig} <- getQueryState
                     io $ debug queryConfig msgs

-- | Generalization of 'Data.SBV.Control.ask'
ask :: (MonadIO m, MonadQuery m) => String -> m String
ask s = do QueryState{queryAsk, queryTimeOutValue} <- getQueryState

           case queryTimeOutValue of
             Nothing -> queryDebug ["[SEND] " `alignPlain` s]
             Just i  -> queryDebug ["[SEND, TimeOut: " ++ showTimeoutValue i ++ "] " `alignPlain` s]
           r <- io $ queryAsk queryTimeOutValue s
           queryDebug ["[RECV] " `alignPlain` r]

           return r

-- | Send a string to the solver, and return the response. Except, if the response
-- is one of the "ignore" ones, keep querying.
askIgnoring :: (MonadIO m, MonadQuery m) => String -> [String] -> m String
askIgnoring s ignoreList = do

           QueryState{queryAsk, queryRetrieveResponse, queryTimeOutValue} <- getQueryState

           case queryTimeOutValue of
             Nothing -> queryDebug ["[SEND] " `alignPlain` s]
             Just i  -> queryDebug ["[SEND, TimeOut: " ++ showTimeoutValue i ++ "] " `alignPlain` s]
           r <- io $ queryAsk queryTimeOutValue s
           queryDebug ["[RECV] " `alignPlain` r]

           let loop currentResponse
                 | currentResponse `notElem` ignoreList
                 = return currentResponse
                 | True
                 = do queryDebug ["[WARN] Previous response is explicitly ignored, beware!"]
                      newResponse <- io $ queryRetrieveResponse queryTimeOutValue
                      queryDebug ["[RECV] " `alignPlain` newResponse]
                      loop newResponse

           loop r

-- | Generalization of 'Data.SBV.Control.send'
send :: (MonadIO m, MonadQuery m) => Bool -> String -> m ()
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

-- | Generalization of 'Data.SBV.Control.retrieveResponse'
retrieveResponse :: (MonadIO m, MonadQuery m) => String -> Maybe Int -> m [String]
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
   sexprToVal (EFloat f)    = Just f
   sexprToVal (ENum (v, _)) = Just (fromIntegral v)
   sexprToVal _             = Nothing

instance SMTValue Double where
   sexprToVal (EDouble f)   = Just f
   sexprToVal (ENum (v, _)) = Just (fromIntegral v)
   sexprToVal _             = Nothing

instance SMTValue Bool where
   sexprToVal (ENum (1, _)) = Just True
   sexprToVal (ENum (0, _)) = Just False
   sexprToVal _             = Nothing

instance SMTValue AlgReal where
   sexprToVal (EReal a)     = Just a
   sexprToVal (ENum (v, _)) = Just (fromIntegral v)
   sexprToVal _             = Nothing

instance SMTValue Char where
   sexprToVal (ENum (i, _)) = Just (chr (fromIntegral i))
   sexprToVal _             = Nothing

instance (SMTValue a, Typeable a) => SMTValue [a] where
   -- NB. The conflation of String/[Char] forces us to have this bastard case here
   -- with unsafeCoerce to cast back to a regular string. This is unfortunate,
   -- and the ice is thin here. But it works, and is much better than a plethora
   -- of overlapping instances. Sigh.
   sexprToVal (ECon s)
    | isKString @[a] undefined && length s >= 2 && head s == '"' && last s == '"'
    = Just $ map unsafeCoerce s'
    | True
    = Just $ map (unsafeCoerce . c2w8) s'
    where s' = qfsToString (tail (init s))
          c2w8  :: Char -> Word8
          c2w8 = fromIntegral . ord

   -- Otherwise we have a good old sequence, just parse it simply:
   sexprToVal (EApp [ECon "seq.++", l, r])            = do l' <- sexprToVal l
                                                           r' <- sexprToVal r
                                                           return $ l' ++ r'
   sexprToVal (EApp [ECon "seq.unit", a])             = do a' <- sexprToVal a
                                                           return [a']
   sexprToVal (EApp [ECon "as", ECon "seq.empty", _]) = return []

   sexprToVal _                                       = Nothing

instance SMTValue () where
   sexprToVal (ECon "SBVTuple0") = Just ()
   sexprToVal _                  = Nothing

-- | Convert a sexpr of n-tuple to constituent sexprs. Z3 and CVC4 differ here on how they
-- present tuples, so we accommodate both:
sexprToTuple :: Int -> SExpr -> [SExpr]
sexprToTuple n e = try e
  where -- Z3 way
        try (EApp (ECon f : args)) = case splitAt (length "mkSBVTuple") f of
                                       ("mkSBVTuple", c) | all isDigit c && read c == n && length args == n -> args
                                       _  -> bad
        -- CVC4 way
        try  (EApp (EApp [ECon "as", ECon f, _] : args)) = try (EApp (ECon f : args))
        try  _ = bad
        bad = error $ "Data.SBV.sexprToTuple: Impossible: Expected a constructor for " ++ show n ++ " tuple, but got: " ++ show e

-- 2-tuple
instance (SMTValue a, SMTValue b) => SMTValue (a, b) where
   sexprToVal s = case sexprToTuple 2 s of
                    [a, b] -> (,) <$> sexprToVal a <*> sexprToVal b
                    _      -> Nothing

-- 3-tuple
instance (SMTValue a, SMTValue b, SMTValue c) => SMTValue (a, b, c) where
   sexprToVal s = case sexprToTuple 3 s of
                    [a, b, c] -> (,,) <$> sexprToVal a <*> sexprToVal b <*> sexprToVal c
                    _         -> Nothing

-- 4-tuple
instance (SMTValue a, SMTValue b, SMTValue c, SMTValue d) => SMTValue (a, b, c, d) where
   sexprToVal s = case sexprToTuple 4 s of
                    [a, b, c, d] -> (,,,) <$> sexprToVal a <*> sexprToVal b <*> sexprToVal c <*> sexprToVal d
                    _            -> Nothing

-- 5-tuple
instance (SMTValue a, SMTValue b, SMTValue c, SMTValue d, SMTValue e) => SMTValue (a, b, c, d, e) where
   sexprToVal s = case sexprToTuple 5 s of
                    [a, b, c, d, e] -> (,,,,) <$> sexprToVal a <*> sexprToVal b <*> sexprToVal c <*> sexprToVal d <*> sexprToVal e
                    _               -> Nothing

-- 6-tuple
instance (SMTValue a, SMTValue b, SMTValue c, SMTValue d, SMTValue e, SMTValue f) => SMTValue (a, b, c, d, e, f) where
   sexprToVal s = case sexprToTuple 6 s of
                    [a, b, c, d, e, f] -> (,,,,,) <$> sexprToVal a <*> sexprToVal b <*> sexprToVal c <*> sexprToVal d <*> sexprToVal e <*> sexprToVal f
                    _                  -> Nothing

-- 7-tuple
instance (SMTValue a, SMTValue b, SMTValue c, SMTValue d, SMTValue e, SMTValue f, SMTValue g) => SMTValue (a, b, c, d, e, f, g) where
   sexprToVal s = case sexprToTuple 7 s of
                    [a, b, c, d, e, f, g] -> (,,,,,,) <$> sexprToVal a <*> sexprToVal b <*> sexprToVal c <*> sexprToVal d <*> sexprToVal e <*> sexprToVal f <*> sexprToVal g
                    _                     -> Nothing

-- 8-tuple
instance (SMTValue a, SMTValue b, SMTValue c, SMTValue d, SMTValue e, SMTValue f, SMTValue g, SMTValue h) => SMTValue (a, b, c, d, e, f, g, h) where
   sexprToVal s = case sexprToTuple 8 s of
                    [a, b, c, d, e, f, g, h] -> (,,,,,,,) <$> sexprToVal a <*> sexprToVal b <*> sexprToVal c <*> sexprToVal d <*> sexprToVal e <*> sexprToVal f <*> sexprToVal g <*> sexprToVal h
                    _                        -> Nothing

-- | Generalization of 'Data.SBV.Control.getValue'
getValue :: (MonadIO m, MonadQuery m, SMTValue a) => SBV a -> m a
getValue s = do sv <- inNewContext (`sbvToSV` s)
                let nm  = show sv
                    cmd = "(get-value (" ++ nm ++ "))"
                    bad = unexpected "getValue" cmd "a model value" Nothing
                r <- ask cmd
                parse r bad $ \case EApp [EApp [ECon o,  v]] | o == show sv -> case sexprToVal v of
                                                                                 Nothing -> bad r Nothing
                                                                                 Just c  -> return c
                                    _                                       -> bad r Nothing

-- | Generalization of 'Data.SBV.Control.getUninterpretedValue'
getUninterpretedValue :: (MonadIO m, MonadQuery m, HasKind a) => SBV a -> m String
getUninterpretedValue s =
        case kindOf s of
          KUninterpreted _ (Left _) -> do sv <- inNewContext (`sbvToSV` s)

                                          let nm  = show sv
                                              cmd = "(get-value (" ++ nm ++ "))"
                                              bad = unexpected "getValue" cmd "a model value" Nothing

                                          r <- ask cmd

                                          parse r bad $ \case EApp [EApp [ECon o,  ECon v]] | o == show sv -> return v
                                                              _                                            -> bad r Nothing

          k                         -> error $ unlines [""
                                                       , "*** SBV.getUninterpretedValue: Called on an 'interpreted' kind"
                                                       , "*** "
                                                       , "***    Kind: " ++ show k
                                                       , "***    Hint: Use 'getValue' to extract value for interpreted kinds."
                                                       , "*** "
                                                       , "*** Only truly uninterpreted sorts should be used with 'getUninterpretedValue.'"
                                                       ]

-- | Get the value of a term, but in CV form. Used internally. The model-index, in particular is extremely Z3 specific!
getValueCVHelper :: (MonadIO m, MonadQuery m) => Maybe Int -> SV -> m CV
getValueCVHelper mbi s
  | s == trueSV
  = return trueCV
  | s == falseSV
  = return falseCV
  | True
  = do let nm  = show s
           k   = kindOf s

           modelIndex = case mbi of
                          Nothing -> ""
                          Just i  -> " :model_index " ++ show i

           cmd        = "(get-value (" ++ nm ++ ")" ++ modelIndex ++ ")"

           bad = unexpected "getModel" cmd ("a value binding for kind: " ++ show k) Nothing

       r <- ask cmd

       parse r bad $ \case EApp [EApp [ECon v, val]] | v == nm -> case recoverKindedValue (kindOf s) val of
                                                                    Just cv -> return cv
                                                                    Nothing -> bad r Nothing
                           _                                   -> bad r Nothing

-- | Recover a given solver-printed value with a possible interpretation
recoverKindedValue :: Kind -> SExpr -> Maybe CV
recoverKindedValue k e = case e of
                           ENum    i | isIntegralLike    -> Just $ mkConstCV k (fst i)
                           ENum    i | isChar          k -> Just $ CV KChar    (CChar    (chr (fromIntegral (fst i))))
                           EReal   i | isReal          k -> Just $ CV KReal    (CAlgReal i)
                           EFloat  i | isFloat         k -> Just $ CV KFloat   (CFloat   i)
                           EDouble i | isDouble        k -> Just $ CV KDouble  (CDouble  i)
                           ECon    s | isString        k -> Just $ CV KString  (CString   (interpretString s))
                           ECon    s | isUninterpreted k -> Just $ CV k        (CUserSort (getUIIndex k s, s))
                           _         | isList          k -> Just $ CV k        (CList     (interpretList e))
                           _         | isTuple         k -> Just $ CV k        (CTuple    (interpretTuple e))

                           _ -> Nothing

  where isIntegralLike = or [f k | f <- [isBoolean, isBounded, isInteger, isReal, isFloat, isDouble]]

        getUIIndex (KUninterpreted  _ (Right xs)) i = i `elemIndex` xs
        getUIIndex _                              _ = Nothing

        stringLike xs = length xs >= 2 && head xs == '"' && last xs == '"'

        -- Make sure strings are really strings
        interpretString xs
          | not (stringLike xs)
          = error $ "Expected a string constant with quotes, received: <" ++ xs ++ ">"
          | True
          = qfsToString $ tail (init xs)

        isStringSequence (KList (KBounded _ 8)) = True
        isStringSequence _                      = False

        -- Lists are tricky since z3 prints the 8-bit variants as strings. See: <http://github.com/Z3Prover/z3/issues/1808>
        interpretList (ECon s)
          | isStringSequence k && stringLike s
          = map (CInteger . fromIntegral . ord) $ interpretString s
        interpretList topExpr = walk topExpr
          where walk (EApp [ECon "as", ECon "seq.empty", _]) = []
                walk (EApp [ECon "seq.unit", v])             = case recoverKindedValue ek v of
                                                                 Just w -> [cvVal w]
                                                                 Nothing -> error $ "Cannot parse a sequence item of kind " ++ show ek ++ " from: " ++ show v ++ extra v
                walk (EApp [ECon "seq.++", pre, post])       = walk pre ++ walk post
                walk cur                                     = error $ "Expected a sequence constant, but received: " ++ show cur ++ extra cur

                extra cur | show cur == t = ""
                          | True          = "\nWhile parsing: " ++ t
                          where t = show topExpr

                ek = case k of
                       KList ik -> ik
                       _        -> error $ "Impossible: Expected a sequence kind, but got: " ++ show k

        interpretTuple te = walk (1 :: Int) (zipWith recoverKindedValue ks args) []
                where (ks, n) = case k of
                                  KTuple eks -> (eks, length eks)
                                  _          -> error $ unlines [ "Impossible: Expected a tuple kind, but got: " ++ show k
                                                                , "While trying to parse: " ++ show te
                                                                ]

                      args = sexprToTuple n te

                      walk _ []           sofar = reverse sofar
                      walk i (Just el:es) sofar = walk (i+1) es (cvVal el : sofar)
                      walk i (Nothing:_)  _     = error $ unlines [ "Couldn't parse a tuple element at position " ++ show i
                                                                  , "Kind: " ++ show k
                                                                  , "Expr: " ++ show te
                                                                  ]

-- | Generalization of 'Data.SBV.Control.getValueCV'
getValueCV :: (MonadIO m, MonadQuery m) => Maybe Int -> SV -> m CV
getValueCV mbi s
  | kindOf s /= KReal
  = getValueCVHelper mbi s
  | True
  = do cfg <- getConfig
       if not (supportsApproxReals (capabilities (solver cfg)))
          then getValueCVHelper mbi s
          else do send True "(set-option :pp.decimal false)"
                  rep1 <- getValueCVHelper mbi s
                  send True   "(set-option :pp.decimal true)"
                  send True $ "(set-option :pp.decimal_precision " ++ show (printRealPrec cfg) ++ ")"
                  rep2 <- getValueCVHelper mbi s

                  let bad = unexpected "getValueCV" "get-value" ("a real-valued binding for " ++ show s) Nothing (show (rep1, rep2)) Nothing

                  case (rep1, rep2) of
                    (CV KReal (CAlgReal a), CV KReal (CAlgReal b)) -> return $ CV KReal (CAlgReal (mergeAlgReals ("Cannot merge real-values for " ++ show s) a b))
                    _                                              -> bad

-- | Generalization of 'Data.SBV.Control.checkSat'
checkSat :: (MonadIO m, MonadQuery m) => m CheckSatResult
checkSat = do cfg <- getConfig
              checkSatUsing $ satCmd cfg

-- | Generalization of 'Data.SBV.Control.checkSatUsing'
checkSatUsing :: (MonadIO m, MonadQuery m) => String -> m CheckSatResult
checkSatUsing cmd = do let bad = unexpected "checkSat" cmd "one of sat/unsat/unknown" Nothing

                           -- Sigh.. Ignore some of the pesky warnings. We only do it as an exception here.
                           ignoreList = ["WARNING: optimization with quantified constraints is not supported"]

                       r <- askIgnoring cmd ignoreList

                       parse r bad $ \case ECon "sat"     -> return Sat
                                           ECon "unsat"   -> return Unsat
                                           ECon "unknown" -> return Unk
                                           _              -> bad r Nothing

-- | What are the top level inputs? Trackers are returned as top level existentials
getQuantifiedInputs :: (MonadIO m, MonadQuery m) => m [(Quantifier, NamedSymVar)]
getQuantifiedInputs = do State{rinps} <- queryState
                         (rQinps, rTrackers) <- liftIO $ readIORef rinps

                         let qinps    = reverse rQinps
                             trackers = map (EX,) $ reverse rTrackers

                             -- separate the existential prefix, which will go first
                             (preQs, postQs) = span (\(q, _) -> q == EX) qinps

                         return $ preQs ++ trackers ++ postQs

-- | Get observables, i.e., those explicitly labeled by the user with a call to 'Data.SBV.observe'.
getObservables :: (MonadIO m, MonadQuery m) => m [(String, CV)]
getObservables = do State{rObservables} <- queryState

                    rObs <- liftIO $ readIORef rObservables

                    -- This intentionally reverses the result; since 'rObs' stores in reversed order
                    let walk []             sofar = return sofar
                        walk ((n, f, s):os) sofar = do cv <- getValueCV Nothing s
                                                       if f cv
                                                          then walk os ((n, cv) : sofar)
                                                          else walk os            sofar

                    walk rObs []

-- | Repeatedly issue check-sat, after refuting the previous model.
-- The bool is true if the model is unique upto prefix existentials.
getAllSatResult :: forall m. (MonadIO m, MonadQuery m, SolverContext m) => m (Bool, Bool, [SMTResult])
getAllSatResult = do queryDebug ["*** Checking Satisfiability, all solutions.."]

                     cfg <- getConfig

                     State{rUsedKinds} <- queryState

                     ki    <- liftIO $ readIORef rUsedKinds
                     qinps <- getQuantifiedInputs

                     let usorts = [s | us@(KUninterpreted s _) <- Set.toList ki, isFree us]

                     unless (null usorts) $ queryDebug [ "*** SBV.allSat: Uninterpreted sorts present: " ++ unwords usorts
                                                       , "***             SBV will use equivalence classes to generate all-satisfying instances."
                                                       ]

                     let vars :: [(SVal, NamedSymVar)]
                         vars = let allModelInputs = takeWhile ((/= ALL) . fst) qinps

                                    sortByNodeId :: [NamedSymVar] -> [NamedSymVar]
                                    sortByNodeId = sortBy (compare `on` (\(SV _ n, _) -> n))

                                    mkSVal :: NamedSymVar -> (SVal, NamedSymVar)
                                    mkSVal nm@(sv, _) = (SVal (kindOf sv) (Right (cache (const (return sv)))), nm)

                                in map mkSVal $ sortByNodeId [nv | (_, nv@(_, n)) <- allModelInputs, not (isNonModelVar cfg n)]

                         -- If we have any universals, then the solutions are unique upto prefix existentials.
                         w = ALL `elem` map fst qinps

                     (sc, ms) <- loop vars cfg
                     return (sc, w, reverse ms)

   where isFree (KUninterpreted _ (Left _)) = True
         isFree _                           = False

         loop vars cfg = go (1::Int) []
           where go :: Int -> [SMTResult] -> m (Bool, [SMTResult])
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
                          Sat   -> do assocs <- mapM (\(sval, (sv, n)) -> do cv <- getValueCV Nothing sv
                                                                             return (n, (sval, cv))) vars

                                      let m = Satisfiable cfg SMTModel { modelObjectives = []
                                                                       , modelAssocs     = [(n, cv) | (n, (_, cv)) <- assocs]
                                                                       }

                                          (interpreteds, uninterpreteds) = partition (not . isFree . kindOf . fst) (map snd assocs)

                                          -- For each "interpreted" variable, figure out the model equivalence
                                          -- NB. When the kind is floating, we *have* to be careful, since +/- zero, and NaN's
                                          -- and equality don't get along!
                                          interpretedEqs :: [SVal]
                                          interpretedEqs = [mkNotEq (kindOf sv) sv (SVal (kindOf sv) (Left cv)) | (sv, cv) <- interpreteds]
                                             where mkNotEq k a b
                                                    | isDouble k || isFloat k = svNot (a `fpNotEq` b)
                                                    | True                    = a `svNotEqual` b

                                                   fpNotEq a b = SVal KBool $ Right $ cache r
                                                       where r st = do swa <- svToSV st a
                                                                       swb <- svToSV st b
                                                                       newExpr st KBool (SBVApp (IEEEFP FP_ObjEqual) [swa, swb])

                                          -- For each "uninterpreted" variable, use equivalence class
                                          uninterpretedEqs :: [SVal]
                                          uninterpretedEqs = concatMap pwDistinct         -- Assert that they are pairwise distinct
                                                           . filter (\l -> length l > 1)  -- Only need this class if it has at least two members
                                                           . map (map fst)                -- throw away values, we only need svals
                                                           . groupBy ((==) `on` snd)      -- make sure they belong to the same sort and have the same value
                                                           . sortOn snd                   -- sort them according to their CV (i.e., sort/value)
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

-- | Generalization of 'Data.SBV.Control.getUnsatAssumptions'
getUnsatAssumptions :: (MonadIO m, MonadQuery m) => [String] -> [(String, a)] -> m [a]
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

-- | Generalization of 'Data.SBV.Control.timeout'
timeout :: (MonadIO m, MonadQuery m) => Int -> m a -> m a
timeout n q = do modifyQueryState (\qs -> qs {queryTimeOutValue = Just n})
                 r <- q
                 modifyQueryState (\qs -> qs {queryTimeOutValue = Nothing})
                 return r

-- | Bail out if a parse goes bad
parse :: String -> (String -> Maybe [String] -> a) -> (SExpr -> a) -> a
parse r fCont sCont = case parseSExpr r of
                        Left  e   -> fCont r (Just [e])
                        Right res -> sCont res

-- | Generalization of 'Data.SBV.Control.unexpected'
unexpected :: (MonadIO m, MonadQuery m) => String -> String -> String -> Maybe [String] -> String -> Maybe [String] -> m a
unexpected ctx sent expected mbHint received mbReason = do
        -- empty the response channel first
        extras <- retrieveResponse "terminating upon unexpected response" (Just 5000000)

        cfg <- getConfig

        let exc = SBVException { sbvExceptionDescription = "Unexpected response from the solver, context: " ++ ctx
                               , sbvExceptionSent        = Just sent
                               , sbvExceptionExpected    = Just expected
                               , sbvExceptionReceived    = Just received
                               , sbvExceptionStdOut      = Just $ unlines extras
                               , sbvExceptionStdErr      = Nothing
                               , sbvExceptionExitCode    = Nothing
                               , sbvExceptionConfig      = cfg
                               , sbvExceptionReason      = mbReason
                               , sbvExceptionHint        = mbHint
                               }

        io $ C.throwIO exc

-- | Convert a query result to an SMT Problem
runProofOn :: SBVRunMode -> QueryContext -> [String] -> Result -> SMTProblem
runProofOn rm context comments res@(Result ki _qcInfo _observables _codeSegs is consts tbls arrs uis axs pgm cstrs _assertions outputs) =
     let (config, isSat, isSafe, isSetup) = case rm of
                                              SMTMode stage s c -> (c, s, isSafetyCheckingIStage stage, isSetupIStage stage)
                                              _                 -> error $ "runProofOn: Unexpected run mode: " ++ show rm

         flipQ (ALL, x) = (EX,  x)
         flipQ (EX,  x) = (ALL, x)

         skolemize :: [(Quantifier, NamedSymVar)] -> [Either SV (SV, [SV])]
         skolemize quants = go quants ([], [])
           where go []                   (_,  sofar) = reverse sofar
                 go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                 go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)

         qinps      = if isSat then fst is else map flipQ (fst is)
         skolemMap  = skolemize qinps

         o | isSafe = trueSV
           | True   = case outputs of
                        []  | isSetup -> trueSV
                        [so]          -> case so of
                                           SV KBool _ -> so
                                           _          -> error $ unlines [ "Impossible happened, non-boolean output: " ++ show so
                                                                         , "Detected while generating the trace:\n" ++ show res
                                                                         ]
                        os  -> error $ unlines [ "User error: Multiple output values detected: " ++ show os
                                               , "Detected while generating the trace:\n" ++ show res
                                               , "*** Check calls to \"output\", they are typically not needed!"
                                               ]

     in SMTProblem { smtLibPgm = toSMTLib config context ki isSat comments is skolemMap consts tbls arrs uis axs pgm cstrs o }

-- | Generalization of 'Data.SBV.Control.executeQuery'
executeQuery :: forall m a. ExtractIO m => QueryContext -> QueryT m a -> SymbolicT m a
executeQuery queryContext (QueryT userQuery) = do
     st <- symbolicEnv
     rm <- liftIO $ readIORef (runMode st)

     -- If we're doing an external query, then we cannot allow quantifiers to be present. Why?
     -- Consider:
     --
     --      issue = do x :: SBool <- forall_
     --                 y :: SBool <- exists_
     --                 constrain y
     --                 query $ do checkSat
     --                         (,) <$> getValue x <*> getValue y
     --
     -- This is the (simplified/annotated SMTLib we would generate:)
     --
     --     (declare-fun s1 (Bool) Bool)   ; s1 is the function that corresponds to the skolemized 'y'
     --     (assert (forall ((s0 Bool))    ; s0 is 'x'
     --                 (s1 s0)))          ; s1 applied to s0 is the actual 'y'
     --     (check-sat)
     --     (get-value (s0))        ; s0 simply not visible here
     --     (get-value (s1))        ; s1 is visible, but only via 's1 s0', so it is also not available.
     --
     -- And that would be terrible! The scoping rules of our "quantified" variables and how they map to
     -- SMTLib is just not compatible. This is a historical design issue, but too late at this point. (We
     -- should've never allowed general quantification like this, but only in limited contexts.)
     --
     -- So, we check if this is an external-query, and if there are quantified variables. If so, we
     -- cowardly refuse to continue. For details, see: <http://github.com/LeventErkok/sbv/issues/407>

     () <- liftIO $ case queryContext of
                      QueryInternal -> return ()         -- we're good, internal usages don't mess with scopes
                      QueryExternal -> do
                        (userInps, _) <- readIORef (rinps st)
                        let badInps = reverse [n | (ALL, (_, n)) <- userInps]
                        case badInps of
                          [] -> return ()
                          _  -> let plu | length badInps > 1 = "s require"
                                        | True               = " requires"
                                in error $ unlines [ ""
                                                   , "*** Data.SBV: Unsupported query call in the presence of quantified inputs."
                                                   , "***"
                                                   , "*** The following variable" ++ plu ++ " explicit quantification: "
                                                   , "***"
                                                   , "***    " ++ intercalate ", " badInps
                                                   , "***"
                                                   , "*** While quantification and queries can co-exist in principle, SBV currently"
                                                   , "*** does not support this scenario. Avoid using quantifiers with user queries"
                                                   , "*** if possible. Please do get in touch if your use case does require such"
                                                   , "*** a feature to see how we can accommodate such scenarios."
                                                   ]

     case rm of
        -- Transitioning from setup
        SMTMode stage isSAT cfg | not (isRunIStage stage) -> do

                                                let backend = engine (solver cfg)

                                                res     <- liftIO $ extractSymbolicSimulationState st
                                                setOpts <- liftIO $ reverse <$> readIORef (rSMTOptions st)

                                                let SMTProblem{smtLibPgm} = runProofOn rm queryContext [] res
                                                    cfg' = cfg { solverSetOptions = solverSetOptions cfg ++ setOpts }
                                                    pgm  = smtLibPgm cfg'

                                                liftIO $ writeIORef (runMode st) $ SMTMode IRun isSAT cfg

                                                lift $ join $ liftIO $ backend cfg' st (show pgm) $
                                                    extractIO . runReaderT userQuery

        -- Already in a query, in theory we can just continue, but that causes use-case issues
        -- so we reject it. TODO: Review if we should actually support this. The issue arises with
        -- expressions like this:
        --
        -- In the following t0's output doesn't get recorded, as the output call is too late when we get
        -- here. (The output field isn't "incremental.") So, t0/t1 behave differently!
        --
        --   t0 = satWith z3{verbose=True, transcript=Just "t.smt2"} $ query (return (false::SBool))
        --   t1 = satWith z3{verbose=True, transcript=Just "t.smt2"} $ ((return (false::SBool)) :: Predicate)
        --
        -- Also, not at all clear what it means to go in an out of query mode:
        --
        -- r = runSMTWith z3{verbose=True} $ do
        --         a' <- sInteger "a"
        --
        --        (a, av) <- query $ do _ <- checkSat
        --                              av <- getValue a'
        --                              return (a', av)
        --
        --        liftIO $ putStrLn $ "Got: " ++ show av
        --        -- constrain $ a .> literal av + 1      -- Cant' do this since we're "out" of query. Sigh.
        --
        --        bv <- query $ do constrain $ a .> literal av + 1
        --                         _ <- checkSat
        --                         getValue a
        --
        --        return $ a' .== a' + 1
        --
        -- This would be one possible implementation, alas it has the problems above:
        --
        --    SMTMode IRun _ _ -> liftIO $ evalStateT userQuery st
        --
        -- So, we just reject it.

        SMTMode IRun _ _ -> error $ unlines [ ""
                                            , "*** Data.SBV: Unsupported nested query is detected."
                                            , "***"
                                            , "*** Please group your queries into one block. Note that this"
                                            , "*** can also arise if you have a call to 'query' not within 'runSMT'"
                                            , "*** For instance, within 'sat'/'prove' calls with custom user queries."
                                            , "*** The solution is to do the sat/prove part in the query directly."
                                            , "***"
                                            , "*** While multiple/nested queries should not be necessary in general,"
                                            , "*** please do get in touch if your use case does require such a feature,"
                                            , "*** to see how we can accommodate such scenarios."
                                            ]

        -- Otherwise choke!
        m -> error $ unlines [ ""
                             , "*** Data.SBV: Invalid query call."
                             , "***"
                             , "***   Current mode: " ++ show m
                             , "***"
                             , "*** Query calls are only valid within runSMT/runSMTWith calls"
                             ]

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
