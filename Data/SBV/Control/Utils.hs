-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Control.Utils
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Query related utils.
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ViewPatterns           #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Control.Utils (
       io
     , ask, send, getValue, getFunction, getUninterpretedValue
     , getValueCV, getUICVal, getUIFunCVAssoc, getUnsatAssumptions
     , SMTFunction(..), registerUISMTFunction
     , getQueryState, modifyQueryState, getConfig, getObjectives, getUIs
     , getSBVAssertions, getSBVPgm, getQuantifiedInputs, getObservables
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

import Data.List  (sortBy, sortOn, elemIndex, partition, groupBy, tails, intercalate, nub, sort)

import Data.Char      (isPunctuation, isSpace, isDigit)
import Data.Function  (on)
import Data.Bifunctor (first)

import Data.Proxy

import qualified Data.Foldable      as F (toList)
import qualified Data.Map.Strict    as Map
import qualified Data.IntMap.Strict as IMap
import qualified Data.Sequence      as S
import qualified Data.Text          as T

import Control.Monad            (join, unless, zipWithM, when, replicateM, forM_)
import Control.Monad.IO.Class   (MonadIO, liftIO)
import Control.Monad.Trans      (lift)
import Control.Monad.Reader     (runReaderT)

import Data.Maybe (isNothing, isJust)

import Data.IORef (readIORef, writeIORef, IORef, newIORef, modifyIORef')

import Data.Time (getZonedTime)
import Data.Ratio

import Data.SBV.Core.Data     ( SV(..), trueSV, falseSV, CV(..), trueCV, falseCV, SBV, sbvToSV, kindOf, Kind(..)
                              , HasKind(..), mkConstCV, CVal(..), SMTResult(..)
                              , NamedSymVar, SMTConfig(..), SMTModel(..)
                              , QueryState(..), SVal(..), Quantifier(..), cache
                              , newExpr, SBVExpr(..), Op(..), FPOp(..), SBV(..), SymArray(..)
                              , SolverContext(..), SBool, Objective(..), SolverCapabilities(..), capabilities
                              , Result(..), SMTProblem(..), trueSV, SymVal(..), SBVPgm(..), SMTSolver(..), SBVRunMode(..)
                              , SBVType(..), forceSVArg, RoundingMode(RoundNearestTiesToEven), (.=>)
                              , RCSet(..)
                              )

import Data.SBV.Core.Symbolic ( IncState(..), withNewIncState, State(..), svToSV, symbolicEnv, SymbolicT
                              , MonadQuery(..), QueryContext(..), Queriable(..), Fresh(..), VarContext(..)
                              , registerLabel, svMkSymVar, validationRequested
                              , isSafetyCheckingIStage, isSetupIStage, isRunIStage, IStage(..), QueryT(..)
                              , extractSymbolicSimulationState, MonadSymbolic(..), newUninterpreted
                              , UserInputs, getInputs, prefixExistentials, getSV, quantifier, getUserName
                              , namedSymVar, NamedSymVar(..), lookupInput, userInputs, userInputsToList
                              , getUserName', Name, CnstMap
                              )

import Data.SBV.Core.AlgReals    (mergeAlgReals, AlgReal(..), RealPoint(..))
import Data.SBV.Core.SizedFloats (fpZero, fpFromInteger, fpFromFloat, fpFromDouble)
import Data.SBV.Core.Kind        (smtType, hasUninterpretedSorts)
import Data.SBV.Core.Operations  (svNot, svNotEqual, svOr, svEqual)

import Data.SBV.SMT.SMT     (showModel, parseCVs, SatModel, AllSatResult(..))
import Data.SBV.SMT.SMTLib  (toIncSMTLib, toSMTLib)
import Data.SBV.SMT.Utils   (showTimeoutValue, addAnnotations, alignPlain, debug, mergeSExpr, SBVException(..))

import Data.SBV.Utils.ExtractIO
import Data.SBV.Utils.Lib       (qfsToString)
import Data.SBV.Utils.SExpr
import Data.SBV.Utils.PrettyNum (cvToSMTLib)

import Data.SBV.Control.Types

import qualified Data.Set as Set (empty, fromList, toAscList)

import qualified Control.Exception as C

import GHC.Stack

-- | 'Data.SBV.Trans.Control.QueryT' as a 'SolverContext'.
instance MonadIO m => SolverContext (QueryT m) where
   constrain              = addQueryConstraint False []
   softConstrain          = addQueryConstraint True  []
   namedConstraint nm     = addQueryConstraint False [(":named", nm)]
   constrainWithAttribute = addQueryConstraint False
   addAxiom               = addQueryAxiom
   contextState           = queryState

   setOption o
     | isStartModeOption o = error $ unlines [ ""
                                             , "*** Data.SBV: '" ++ show o ++ "' can only be set at start-up time."
                                             , "*** Hint: Move the call to 'setOption' before the query."
                                             ]
     | True                = send True $ setSMTOption o

   addSMTDefinition nm _ = error $ unlines [ ""
                                           , "*** Data.SBV: '" ++ show nm ++ "' must be defined in regular (non-query) mode."
                                           , "*** Hint: Define all functions before starting the query."
                                           ]

-- | Adding a constraint, possibly with attributes and possibly soft. Only used internally.
-- Use 'constrain' and 'namedConstraint' from user programs.
addQueryConstraint :: (MonadIO m, MonadQuery m) => Bool -> [(String, String)] -> SBool -> m ()
addQueryConstraint isSoft atts b = do sv <- inNewContext (\st -> liftIO $ do mapM_ (registerLabel "Constraint" st) [nm | (":named", nm) <- atts]
                                                                             sbvToSV st b)

                                      unless (null atts && sv == trueSV) $
                                             send True $ "(" ++ asrt ++ " " ++ addAnnotations atts (show sv)  ++ ")"
   where asrt | isSoft = "assert-soft"
              | True   = "assert"

addQueryAxiom :: (MonadIO m, MonadQuery m) => String -> [String] -> m ()
addQueryAxiom nm ls = do send True $ "; -- user given axiom: " ++ nm
                         send True $ intercalate "\n" ls

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
syncUpSolver :: (MonadIO m, MonadQuery m) => IORef CnstMap -> IncState -> m ()
syncUpSolver rGlobalConsts is = do
        cfg <- getConfig

        -- update global consts to have the new ones
        (newConsts, allConsts) <- liftIO $ do nc <- readIORef (rNewConsts is)
                                              oc <- readIORef rGlobalConsts
                                              let allConsts = Map.union nc oc
                                              writeIORef rGlobalConsts allConsts
                                              pure (nc, allConsts)

        ls  <- io $ do let swap  (a, b)        = (b, a)
                           cmp   (a, _) (b, _) = a `compare` b
                           arrange (i, (at, rt, es)) = ((i, at, rt), es)
                       inps        <- reverse <$> readIORef (rNewInps is)
                       ks          <- readIORef (rNewKinds is)
                       arrs        <- IMap.toAscList <$> readIORef (rNewArrs is)
                       tbls        <- map arrange . sortBy cmp . map swap . Map.toList <$> readIORef (rNewTbls is)
                       uis         <- Map.toAscList <$> readIORef (rNewUIs is)
                       as          <- readIORef (rNewAsgns is)
                       constraints <- readIORef (rNewConstraints is)

                       let cnsts = sortBy cmp . map swap . Map.toList $ newConsts

                       return $ toIncSMTLib cfg inps ks (allConsts, cnsts) arrs tbls uis as constraints cfg
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
inNewContext act = do st@State{rconstMap} <- queryState
                      (is, r) <- io $ withNewIncState st act
                      syncUpSolver rconstMap is
                      return r

-- | Generic 'Queriable' instance for 'SymVal' values
instance (MonadIO m, SymVal a) => Queriable m (SBV a) a where
  create  = freshVar_
  project = getValue
  embed   = return . literal

-- | Generic 'Queriable' instance for things that are 'Fresh' and look like containers:
instance (MonadIO m, SymVal a, Foldable t, Traversable t, Fresh m (t (SBV a))) => Queriable m (t (SBV a)) (t a) where
  create  = fresh
  project = mapM getValue
  embed   = return . fmap literal

-- | Generalization of 'Data.SBV.Control.freshVar_'
freshVar_ :: forall a m. (MonadIO m, MonadQuery m, SymVal a) => m (SBV a)
freshVar_ = inNewContext $ fmap SBV . svMkSymVar QueryVar k Nothing
  where k = kindOf (Proxy @a)

-- | Generalization of 'Data.SBV.Control.freshVar'
freshVar :: forall a m. (MonadIO m, MonadQuery m, SymVal a) => String -> m (SBV a)
freshVar nm = inNewContext $ fmap SBV . svMkSymVar QueryVar k (Just nm)
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

               else do -- fire and forget. if you use this, you're on your own!
                       queryDebug ["[FIRE] " `alignPlain` s]
                       io $ querySend queryTimeOutValue s

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

-- | Generalization of 'Data.SBV.Control.getValue'
getValue :: (MonadIO m, MonadQuery m, SymVal a) => SBV a -> m a
getValue s = do sv <- inNewContext (`sbvToSV` s)
                cv <- getValueCV Nothing sv
                return $ fromCV cv

-- | A class which allows for sexpr-conversion to functions
class (HasKind r, SatModel r) => SMTFunction fun a r | fun -> a r where
  sexprToArg     :: fun -> [SExpr] -> Maybe a
  smtFunName     :: (MonadIO m, SolverContext m, MonadSymbolic m) => fun -> m String
  smtFunSaturate :: fun -> SBV r
  smtFunType     :: fun -> SBVType
  smtFunDefault  :: fun -> Maybe r
  sexprToFun     :: (MonadIO m, SolverContext m, MonadQuery m, MonadSymbolic m, SymVal r) => fun -> SExpr -> m (Maybe ([(a, r)], r))

  {-# MINIMAL sexprToArg, smtFunSaturate, smtFunType  #-}

  -- Given the function, figure out a default "return value"
  smtFunDefault _
    | Just v <- defaultKindedValue (kindOf (Proxy @r)), Just (res, []) <- parseCVs [v]
    = Just res
    | True
    = Nothing

  -- Given the function, determine what its name is and do some sanity checks
  smtFunName f = do st@State{rUIMap} <- contextState
                    uiMap <- liftIO $ readIORef rUIMap
                    findName st uiMap
    where findName st@State{spgm} uiMap = do
             r <- liftIO $ sbvToSV st (smtFunSaturate f)
             liftIO $ forceSVArg r
             SBVPgm asgns <- liftIO $ readIORef spgm

             let cantFind = error $ unlines $    [ ""
                                                 , "*** Data.SBV.getFunction: Must be called on an uninterpreted function!"
                                                 , "***"
                                                 , "***    Expected to receive a function created by \"uninterpret\""
                                                 ]
                                              ++ tag
                                              ++ [ "***"
                                                 , "*** Make sure to call getFunction on uninterpreted functions only!"
                                                 , "*** If that is already the case, please report this as a bug."
                                                 ]
                      where tag = case map fst (Map.toList uiMap) of
                                    []    -> [ "***    But, there are no matching uninterpreted functions in the context." ]
                                    [x]   -> [ "***    The only possible candidate is: " ++ x ]
                                    cands -> [ "***    Candidates are:"
                                             , "***        " ++ intercalate ", " cands
                                             ]

             case S.findIndexR ((== r) . fst) asgns of
               Nothing -> cantFind
               Just i  -> case asgns `S.index` i of
                            (sv, SBVApp (Uninterpreted nm) _) | r == sv -> return nm
                            _                                           -> cantFind

  sexprToFun f e = do nm <- smtFunName f
                      case parseSExprFunction e of
                        Just (Left nm') -> case (nm == nm', smtFunDefault f) of
                                             (True, Just v)  -> return $ Just ([], v)
                                             _               -> bailOut nm
                        Just (Right v)  -> return $ convert v
                        Nothing         -> do mbPVS <- pointWiseExtract nm (smtFunType f)
                                              return $ mbPVS >>= convert
    where convert    (vs, d) = (,) <$> mapM sexprPoint vs <*> sexprToVal d
          sexprPoint (as, v) = (,) <$> sexprToArg f as    <*> sexprToVal v

          bailOut nm = error $ unlines [ ""
                                       , "*** Data.SBV.getFunction: Unable to extract an interpretation for function " ++ show nm
                                       , "***"
                                       , "*** Failed while trying to extract a pointwise interpretation."
                                       , "***"
                                       , "*** This could be a bug with SBV or the backend solver. Please report!"
                                       ]

-- | Registering an uninterpreted SMT function. This is typically not necessary as uses of the UI
-- function itself will register it automatically. But there are cases where doing this explicitly can
-- come in handy.
registerUISMTFunction :: (MonadIO m, SolverContext m, MonadSymbolic m) => SMTFunction fun a r => fun -> m ()
registerUISMTFunction f = do st <- contextState
                             nm <- smtFunName f
                             io $ newUninterpreted st nm (smtFunType f) Nothing

-- | Pointwise function value extraction. If we get unlucky and can't parse z3's output (happens
-- when we have all booleans and z3 decides to spit out an expression), just brute force our
-- way out of it. Note that we only do this if we have a pure boolean type, as otherwise we'd blow
-- up. And I think it'll only be necessary then, I haven't seen z3 try anything smarter in other scenarios.
pointWiseExtract ::  forall m. (MonadIO m, MonadQuery m) => String -> SBVType -> m (Maybe ([([SExpr], SExpr)], SExpr))
pointWiseExtract nm typ
   | isBoolFunc
   = tryPointWise
   | True
   = error $ unlines [ ""
                     , "*** Data.SBV.getFunction: Unsupported: Extracting interpretation for function:"
                     , "***"
                     , "***     " ++ nm ++ " :: " ++ show typ
                     , "***"
                     , "*** At this time, the expression returned by the solver is too complicated for SBV!"
                     , "***"
                     , "*** You can ignore uninterpreted function models for sat models using the 'satTrackUFs' parameter:"
                     , "***"
                     , "***             satWith    z3{satTrackUFs = False}"
                     , "***             allSatWith z3{satTrackUFs = False}"
                     , "***"
                     , "*** You can see the response from the solver by running with '{verbose = True}' option."
                     , "***"
                     , "*** NB. If this is a use case you'd like SBV to support, please get in touch!"
                     ]
  where trueSExpr  = ENum (1, Nothing)
        falseSExpr = ENum (0, Nothing)

        isTrueSExpr (ENum (1, Nothing)) = True
        isTrueSExpr (ENum (0, Nothing)) = False
        isTrueSExpr s                   = error $ "Data.SBV.pointWiseExtract: Impossible happened: Received: " ++ show s

        (nArgs, isBoolFunc) = case typ of
                                SBVType ts -> (length ts - 1, all (== KBool) ts)

        getBVal :: [SExpr] -> m ([SExpr], SExpr)
        getBVal args = do let shc c | isTrueSExpr c = "true"
                                    | True          = "false"

                              as = unwords $ map shc args

                              cmd   = "(get-value ((" ++ nm ++ " " ++ as ++ ")))"

                              bad   = unexpected "get-value" cmd ("pointwise value of boolean function " ++ nm ++ " on " ++ show as) Nothing

                          r <- ask cmd

                          parse r bad $ \case EApp [EApp [_, e]] -> return (args, e)
                                              _                  -> bad r Nothing

        getBVals :: m [([SExpr], SExpr)]
        getBVals = mapM getBVal $ replicateM nArgs [falseSExpr, trueSExpr]

        tryPointWise
          | not isBoolFunc
          = return Nothing
          | nArgs < 1
          = error $ "Data.SBV.pointWiseExtract: Impossible happened, nArgs < 1: " ++ show nArgs ++ " type: " ++ show typ
          | True
          = do vs <- getBVals
               -- Pick the value that will give us the fewer entries
               let (trues, falses) = partition (\(_, v) -> isTrueSExpr v) vs
               return $ Just $ if length trues <= length falses
                               then (trues,  falseSExpr)
                               else (falses, trueSExpr)

-- | For saturation purposes, get a proper argument. The forall quantification
-- is safe here since we only use in smtFunSaturate calls, which looks at the
-- kind stored inside only.
mkArg :: forall a. Kind -> SBV a
mkArg k = case defaultKindedValue k of
            Nothing -> error $ unlines [ ""
                                       , "*** Data.SBV.smtFunSaturate: Impossible happened!"
                                       , "*** Unable to create a valid parameter for kind: " ++ show k
                                       , "*** Please report this as an SBV bug!"
                                       ]
            Just c -> SBV $ SVal k (Left c)

-- | Functions of arity 1
instance ( SymVal a, HasKind a
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV r) a r
         where
  sexprToArg _ [a0] = sexprToVal a0
  sexprToArg _ _    = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @r)]

  smtFunSaturate f = f $ mkArg (kindOf (Proxy @a))

-- | Functions of arity 2
instance ( SymVal a,  HasKind a
         , SymVal b,  HasKind b
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV b -> SBV r) (a, b) r
         where
  sexprToArg _ [a0, a1] = (,) <$> sexprToVal a0 <*> sexprToVal a1
  sexprToArg _ _        = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @r)]

  smtFunSaturate f = f (mkArg (kindOf (Proxy @a)))
                       (mkArg (kindOf (Proxy @b)))

-- | Functions of arity 3
instance ( SymVal a,   HasKind a
         , SymVal b,   HasKind b
         , SymVal c,   HasKind c
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV b -> SBV c -> SBV r) (a, b, c) r
         where
  sexprToArg _ [a0, a1, a2] = (,,) <$> sexprToVal a0 <*> sexprToVal a1 <*> sexprToVal a2
  sexprToArg _ _            = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @r)]

  smtFunSaturate f = f (mkArg (kindOf (Proxy @a)))
                       (mkArg (kindOf (Proxy @b)))
                       (mkArg (kindOf (Proxy @c)))

-- | Functions of arity 4
instance ( SymVal a,   HasKind a
         , SymVal b,   HasKind b
         , SymVal c,   HasKind c
         , SymVal d,   HasKind d
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV b -> SBV c -> SBV d -> SBV r) (a, b, c, d) r
         where
  sexprToArg _ [a0, a1, a2, a3] = (,,,) <$> sexprToVal a0 <*> sexprToVal a1 <*> sexprToVal a2 <*> sexprToVal a3
  sexprToArg _ _               = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @r)]

  smtFunSaturate f = f (mkArg (kindOf (Proxy @a)))
                       (mkArg (kindOf (Proxy @b)))
                       (mkArg (kindOf (Proxy @c)))
                       (mkArg (kindOf (Proxy @d)))

-- | Functions of arity 5
instance ( SymVal a,   HasKind a
         , SymVal b,   HasKind b
         , SymVal c,   HasKind c
         , SymVal d,   HasKind d
         , SymVal e,   HasKind e
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV r) (a, b, c, d, e) r
         where
  sexprToArg _ [a0, a1, a2, a3, a4] = (,,,,) <$> sexprToVal a0 <*> sexprToVal a1 <*> sexprToVal a2 <*> sexprToVal a3 <*> sexprToVal a4
  sexprToArg _ _                    = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @r)]

  smtFunSaturate f = f (mkArg (kindOf (Proxy @a)))
                       (mkArg (kindOf (Proxy @b)))
                       (mkArg (kindOf (Proxy @c)))
                       (mkArg (kindOf (Proxy @d)))
                       (mkArg (kindOf (Proxy @e)))

-- | Functions of arity 6
instance ( SymVal a,   HasKind a
         , SymVal b,   HasKind b
         , SymVal c,   HasKind c
         , SymVal d,   HasKind d
         , SymVal e,   HasKind e
         , SymVal f,   HasKind f
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV r) (a, b, c, d, e, f) r
         where
  sexprToArg _ [a0, a1, a2, a3, a4, a5] = (,,,,,) <$> sexprToVal a0 <*> sexprToVal a1 <*> sexprToVal a2 <*> sexprToVal a3 <*> sexprToVal a4 <*> sexprToVal a5
  sexprToArg _ _                        = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f), kindOf (Proxy @r)]

  smtFunSaturate f = f (mkArg (kindOf (Proxy @a)))
                       (mkArg (kindOf (Proxy @b)))
                       (mkArg (kindOf (Proxy @c)))
                       (mkArg (kindOf (Proxy @d)))
                       (mkArg (kindOf (Proxy @e)))
                       (mkArg (kindOf (Proxy @f)))

-- | Functions of arity 7
instance ( SymVal a,   HasKind a
         , SymVal b,   HasKind b
         , SymVal c,   HasKind c
         , SymVal d,   HasKind d
         , SymVal e,   HasKind e
         , SymVal f,   HasKind f
         , SymVal g,   HasKind g
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV g -> SBV r) (a, b, c, d, e, f, g) r
         where
  sexprToArg _ [a0, a1, a2, a3, a4, a5, a6] = (,,,,,,) <$> sexprToVal a0 <*> sexprToVal a1 <*> sexprToVal a2 <*> sexprToVal a3 <*> sexprToVal a4 <*> sexprToVal a5 <*> sexprToVal a6
  sexprToArg _ _                            = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f), kindOf (Proxy @g), kindOf (Proxy @r)]

  smtFunSaturate f = f (mkArg (kindOf (Proxy @a)))
                       (mkArg (kindOf (Proxy @b)))
                       (mkArg (kindOf (Proxy @c)))
                       (mkArg (kindOf (Proxy @d)))
                       (mkArg (kindOf (Proxy @e)))
                       (mkArg (kindOf (Proxy @f)))
                       (mkArg (kindOf (Proxy @g)))

-- | Functions of arity 8
instance ( SymVal a,   HasKind a
         , SymVal b,   HasKind b
         , SymVal c,   HasKind c
         , SymVal d,   HasKind d
         , SymVal e,   HasKind e
         , SymVal f,   HasKind f
         , SymVal g,   HasKind g
         , SymVal h,   HasKind h
         , SatModel r, HasKind r
         ) => SMTFunction (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV g -> SBV h -> SBV r) (a, b, c, d, e, f, g, h) r
         where
  sexprToArg _ [a0, a1, a2, a3, a4, a5, a6, a7] = (,,,,,,,) <$> sexprToVal a0 <*> sexprToVal a1 <*> sexprToVal a2 <*> sexprToVal a3 <*> sexprToVal a4 <*> sexprToVal a5 <*> sexprToVal a6 <*> sexprToVal a7
  sexprToArg _ _                                = Nothing

  smtFunType _ = SBVType [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f), kindOf (Proxy @g), kindOf (Proxy @h), kindOf (Proxy @r)]

  smtFunSaturate f = f (mkArg (kindOf (Proxy @a)))
                       (mkArg (kindOf (Proxy @b)))
                       (mkArg (kindOf (Proxy @c)))
                       (mkArg (kindOf (Proxy @d)))
                       (mkArg (kindOf (Proxy @e)))
                       (mkArg (kindOf (Proxy @f)))
                       (mkArg (kindOf (Proxy @g)))
                       (mkArg (kindOf (Proxy @h)))

-- | Generalization of 'Data.SBV.Control.getFunction'
getFunction :: (MonadIO m, MonadQuery m, SolverContext m, MonadSymbolic m, SymVal a, SymVal r, SMTFunction fun a r) => fun -> m ([(a, r)], r)
getFunction f = do nm <- smtFunName f

                   let cmd = "(get-value (" ++ nm ++ "))"
                       bad = unexpected "getFunction" cmd "a function value" Nothing

                   r <- ask cmd

                   parse r bad $ \case EApp [EApp [ECon o, e]] | o == nm -> do mbAssocs <- sexprToFun f e
                                                                               case mbAssocs of
                                                                                 Just assocs -> return assocs
                                                                                 Nothing     -> do mbPVS <- pointWiseExtract nm (smtFunType f)
                                                                                                   case mbPVS >>= convert of
                                                                                                     Just x  -> return x
                                                                                                     Nothing -> bad r Nothing
                                       _                                 -> bad r Nothing
    where convert    (vs, d) = (,) <$> mapM sexprPoint vs <*> sexprToVal d
          sexprPoint (as, v) = (,) <$> sexprToArg f as    <*> sexprToVal v

-- | Generalization of 'Data.SBV.Control.getUninterpretedValue'
getUninterpretedValue :: (MonadIO m, MonadQuery m, HasKind a) => SBV a -> m String
getUninterpretedValue s =
        case kindOf s of
          KUserSort _ Nothing -> do sv <- inNewContext (`sbvToSV` s)

                                    let nm  = show sv
                                        cmd = "(get-value (" ++ nm ++ "))"
                                        bad = unexpected "getValue" cmd "a model value" Nothing

                                    r <- ask cmd

                                    parse r bad $ \case EApp [EApp [ECon o,  ECon v]] | o == show sv -> return v
                                                        _                                            -> bad r Nothing

          k                   -> error $ unlines [""
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
  = extractValue mbi (show s) (kindOf s)

-- | "Make up" a CV for this type. Like zero, but smarter.
defaultKindedValue :: Kind -> Maybe CV
defaultKindedValue k = CV k <$> cvt k
  where cvt :: Kind -> Maybe CVal
        cvt KBool            = Just $ CInteger 0
        cvt KBounded{}       = Just $ CInteger 0
        cvt KUnbounded       = Just $ CInteger 0
        cvt KReal            = Just $ CAlgReal 0
        cvt (KUserSort _ ui) = uninterp ui
        cvt KFloat           = Just $ CFloat 0
        cvt KDouble          = Just $ CDouble 0
        cvt KRational        = Just $ CRational 0
        cvt (KFP eb sb)      = Just $ CFP (fpZero False eb sb)
        cvt KChar            = Just $ CChar '\NUL'                -- why not?
        cvt KString          = Just $ CString ""
        cvt (KList  _)       = Just $ CList []
        cvt (KSet  _)        = Just $ CSet $ RegularSet Set.empty -- why not? Arguably, could be the universal set
        cvt (KTuple ks)      = CTuple <$> mapM cvt ks
        cvt (KMaybe _)       = Just $ CMaybe Nothing
        cvt (KEither k1 _)   = CEither . Left <$> cvt k1          -- why not?

        -- Tricky case of uninterpreted
        uninterp (Just (c:_)) = Just $ CUserSort (Just 1, c)
        uninterp (Just [])    = Nothing                       -- I don't think this can actually happen, but just in case
        uninterp Nothing      = Nothing                       -- Out of luck, truly uninterpreted; we don't even know if it's inhabited.

-- | Go from an SExpr directly to a value
sexprToVal :: forall a. SymVal a => SExpr -> Maybe a
sexprToVal e = fromCV <$> recoverKindedValue (kindOf (Proxy @a)) e

-- | Recover a given solver-printed value with a possible interpretation
recoverKindedValue :: Kind -> SExpr -> Maybe CV
recoverKindedValue k e = case k of
                           KBool       | ENum (i, _) <- e      -> Just $ mkConstCV k i
                                       | True                  -> Nothing

                           KBounded{}  | ENum (i, _) <- e      -> Just $ mkConstCV k i
                                       | True                  -> Nothing

                           KUnbounded  | ENum (i, _) <- e      -> Just $ mkConstCV k i
                                       | True                  -> Nothing

                           KReal       | ENum (i, _) <- e      -> Just $ mkConstCV k i
                                       | EReal i     <- e      -> Just $ CV KReal (CAlgReal i)
                                       | True                  -> interpretInterval e

                           KUserSort{} | ECon s <- e           -> Just $ CV k $ CUserSort (getUIIndex k s, s)
                                       | True                  -> Nothing

                           KFloat      | ENum (i, _) <- e      -> Just $ mkConstCV k i
                                       | EFloat i    <- e      -> Just $ CV KFloat (CFloat i)
                                       | True                  -> Nothing

                           KDouble     | ENum (i, _) <- e      -> Just $ mkConstCV k i
                                       | EDouble i   <- e      -> Just $ CV KDouble (CDouble i)
                                       | True                  -> Nothing

                           KFP eb sb   | ENum (i, _)      <- e -> Just $ CV k $ CFP $ fpFromInteger eb sb i
                                       | EFloat f         <- e -> Just $ CV k $ CFP $ fpFromFloat   eb sb f
                                       | EDouble d        <- e -> Just $ CV k $ CFP $ fpFromDouble  eb sb d
                                       | EFloatingPoint c <- e -> Just $ CV k $ CFP c
                                       | True                  -> Nothing

                           KChar       | ECon s      <- e      -> Just $ CV KChar $ CChar $ interpretChar s
                                       | True                  -> Nothing

                           KString     | ECon s      <- e      -> Just $ CV KString $ CString $ interpretString s
                                       | True                  -> Nothing

                           KRational                           -> Just $ CV k $ CRational $ interpretRational e

                           KList ek                            -> Just $ CV k $ CList $ interpretList ek e

                           KSet ek                             -> Just $ CV k $ CSet $ interpretSet ek e

                           KTuple{}                            -> Just $ CV k $ CTuple $ interpretTuple e

                           KMaybe{}                            -> Just $ CV k $ CMaybe $ interpretMaybe k e

                           KEither{}                           -> Just $ CV k $ CEither $ interpretEither k e

  where getUIIndex (KUserSort  _ (Just xs)) i = i `elemIndex` xs
        getUIIndex _                        _ = Nothing

        stringLike xs = length xs >= 2 && head xs == '"' && last xs == '"'

        -- Make sure strings are really strings
        interpretString xs
          | not (stringLike xs)
          = error $ "Expected a string constant with quotes, received: <" ++ xs ++ ">"
          | True
          = qfsToString $ tail (init xs)

        interpretChar xs = case interpretString xs of
                             [c] -> c
                             _   -> error $ "Expected a singleton char constant, received: <" ++ xs ++ ">"

        interpretRational (EApp [ECon "SBV.Rational", v1, v2])
           | Just (CV _ (CInteger n)) <- recoverKindedValue KUnbounded v1
           , Just (CV _ (CInteger d)) <- recoverKindedValue KUnbounded v2
           = n % d
        interpretRational xs = error $ "Expected a rational constant, received: <" ++ show xs ++ ">"

        interpretList ek topExpr = walk topExpr
          where walk (EApp [ECon "as", ECon "seq.empty", _]) = []
                walk (EApp [ECon "seq.unit", v])             = case recoverKindedValue ek v of
                                                                 Just w -> [cvVal w]
                                                                 Nothing -> error $ "Cannot parse a sequence item of kind " ++ show ek ++ " from: " ++ show v ++ extra v
                walk (EApp (ECon "seq.++" : rest))           = concatMap walk rest
                walk cur                                     = error $ "Expected a sequence constant, but received: " ++ show cur ++ extra cur

                extra cur | show cur == t = ""
                          | True          = "\nWhile parsing: " ++ t
                          where t = show topExpr

        -- Essentially treat sets as functions, since we do allow for store associations
        interpretSet ke setExpr
             | isUniversal setExpr             = ComplementSet Set.empty
             | isEmpty     setExpr             = RegularSet    Set.empty
             | Just (Right assocs) <- mbAssocs = decode assocs
             | True                            = tbd "Expected a set value, but couldn't decipher the solver output."

           where tbd w = error $ unlines [ ""
                                         , "*** Data.SBV.interpretSet: Unable to process solver output."
                                         , "***"
                                         , "*** Kind    : " ++ show (KSet ke)
                                         , "*** Received: " ++ show setExpr
                                         , "*** Reason  : " ++ w
                                         , "***"
                                         , "*** This is either a bug or something SBV currently does not support."
                                         , "*** Please report this as a feature request!"
                                         ]


                 isTrue (ENum (1, Nothing)) = True
                 isTrue (ENum (0, Nothing)) = False
                 isTrue bad                 = tbd $ "Non-boolean membership value seen: " ++ show bad

                 isUniversal (EApp [EApp [ECon "as", ECon "const", EApp [ECon "Array", _, ECon "Bool"]], r]) = isTrue r
                 isUniversal _                                                                               = False

                 isEmpty     (EApp [EApp [ECon "as", ECon "const", EApp [ECon "Array", _, ECon "Bool"]], r]) = not $ isTrue r
                 isEmpty     _                                                                               = False

                 mbAssocs = parseSExprFunction setExpr

                 decode (args, r) | isTrue r = ComplementSet $ Set.fromList [x | (x, False) <- concatMap (contents True)  args]  -- deletions from universal
                                  | True     = RegularSet    $ Set.fromList [x | (x, True)  <- concatMap (contents False) args]  -- additions to empty

                 contents cvt ([v], r) = let t = isTrue r in map (, t) (element cvt v)
                 contents _   bad      = tbd $ "Multi-valued set member seen: " ++ show bad

                 element cvt x = case (cvt, ke) of
                                   (True, KChar) -> case recoverKindedValue KString x of
                                                      Just v  -> case cvVal v of
                                                                  CString [c] -> [CChar c]
                                                                  CString _   -> []
                                                                  _           -> tbd $ "Unexpected value for kind: " ++ show (x, ke)
                                                      Nothing -> tbd $ "Unexpected value for kind: " ++ show (x, ke)
                                   _             -> case recoverKindedValue ke x of
                                                      Just v  -> [cvVal v]
                                                      Nothing -> tbd $ "Unexpected value for kind: " ++ show (x, ke)

        interpretTuple te = walk (1 :: Int) (zipWith recoverKindedValue ks args) []
                where (ks, n) = case k of
                                  KTuple eks -> (eks, length eks)
                                  _          -> error $ unlines [ "Impossible: Expected a tuple kind, but got: " ++ show k
                                                                , "While trying to parse: " ++ show te
                                                                ]

                      -- | Convert a sexpr of n-tuple to constituent sexprs. Z3 and CVC4 differ here on how they
                      -- present tuples, so we accommodate both:
                      args = try te
                        where -- Z3 way
                              try (EApp (ECon f : as)) = case splitAt (T.length "mkSBVTuple") f of
                                                             ("mkSBVTuple", c) | all isDigit c && read c == n && length as == n -> as
                                                             _  -> bad
                              -- CVC4 way
                              try  (EApp (EApp [ECon "as", ECon f, _] : as)) = try (EApp (ECon f : as))
                              try  _ = bad
                              bad = error $ "Data.SBV.sexprToTuple: Impossible: Expected a constructor for " ++ show n ++ " tuple, but got: " ++ show te

                      walk _ []           sofar = reverse sofar
                      walk i (Just el:es) sofar = walk (i+1) es (cvVal el : sofar)
                      walk i (Nothing:_)  _     = error $ unlines [ "Couldn't parse a tuple element at position " ++ show i
                                                                  , "Kind: " ++ show k
                                                                  , "Expr: " ++ show te
                                                                  ]

        -- SMaybe
        interpretMaybe (KMaybe _)  (ECon "nothing_SBVMaybe")        = Nothing
        interpretMaybe (KMaybe ek) (EApp [ECon "just_SBVMaybe", a]) = case recoverKindedValue ek a of
                                                                        Just (CV _ v) -> Just v
                                                                        Nothing       -> error $ unlines [ "Couldn't parse a maybe just value"
                                                                                                         , "Kind: " ++ show ek
                                                                                                         , "Expr: " ++ show a
                                                                                                         ]
        -- CVC4 puts in full ascriptions, handle those:
        interpretMaybe _  (      EApp [ECon "as", ECon "nothing_SBVMaybe", _])     = Nothing
        interpretMaybe mk (EApp [EApp [ECon "as", ECon "just_SBVMaybe",    _], a]) = interpretMaybe mk (EApp [ECon "just_SBVMaybe", a])

        interpretMaybe _  other = error $ "Expected an SMaybe sexpr, but received: " ++ show (k, other)

        -- SEither
        interpretEither (KEither k1 _) (EApp [ECon "left_SBVEither",  a]) = case recoverKindedValue k1 a of
                                                                              Just (CV _ v) -> Left v
                                                                              Nothing       -> error $ unlines [ "Couldn't parse an either value on the left"
                                                                                                               , "Kind: " ++ show k1
                                                                                                               , "Expr: " ++ show a
                                                                                                               ]
        interpretEither (KEither _ k2) (EApp [ECon "right_SBVEither", b]) = case recoverKindedValue k2 b of
                                                                              Just (CV _ v) -> Right v
                                                                              Nothing       -> error $ unlines [ "Couldn't parse an either value on the right"
                                                                                                               , "Kind: " ++ show k2
                                                                                                               , "Expr: " ++ show b
                                                                                                               ]

        -- CVC4 puts full ascriptions:
        interpretEither ek (EApp [EApp [ECon "as", ECon "left_SBVEither",  _], a]) = interpretEither ek (EApp [ECon "left_SBVEither", a])
        interpretEither ek (EApp [EApp [ECon "as", ECon "right_SBVEither", _], b]) = interpretEither ek (EApp [ECon "right_SBVEither", b])

        interpretEither _ other = error $ "Expected an SEither sexpr, but received: " ++ show (k, other)

        -- Intervals, for dReal
        interpretInterval expr = case expr of
                                   EApp [ECon "interval", lo, hi] -> do vlo <- getBorder lo
                                                                        vhi <- getBorder hi
                                                                        pure $ CV KReal (CAlgReal (AlgInterval vlo vhi))
                                   _                              -> Nothing
          where getBorder (EApp [ECon "open",   v]) = recoverKindedValue KReal v >>= border OpenPoint
                getBorder (EApp [ECon "closed", v]) = recoverKindedValue KReal v >>= border ClosedPoint
                getBorder _                         = Nothing

                border b (CV KReal (CAlgReal (AlgRational True v))) = pure $ b v
                border _ other                                      = error $ "Data.SBV.interpretInterval.border: Expected a real-valued sexp, but received: " ++ show other


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

-- | Retrieve value from the solver
extractValue :: forall m. (MonadIO m, MonadQuery m) => Maybe Int -> String -> Kind -> m CV
extractValue mbi nm k = do
       let modelIndex = case mbi of
                          Nothing -> ""
                          Just i  -> " :model_index " ++ show i

           cmd        = "(get-value (" ++ nm ++ ")" ++ modelIndex ++ ")"

           bad = unexpected "getModel" cmd ("a value binding for kind: " ++ show k) Nothing

       r <- ask cmd

       let recover val = case recoverKindedValue k val of
                           Just cv -> return cv
                           Nothing -> bad r Nothing

       parse r bad $ \case EApp [EApp [ECon v, val]] | v == nm -> recover val
                           _                                   -> bad r Nothing

-- | Generalization of 'Data.SBV.Control.getUICVal'
getUICVal :: forall m. (MonadIO m, MonadQuery m) => Maybe Int -> (String, SBVType) -> m CV
getUICVal mbi (nm, t) = case t of
                          SBVType [k] -> extractValue mbi nm k
                          _           -> error $ "SBV.getUICVal: Expected to be called on an uninterpeted value of a base type, received something else: " ++ show (nm, t)

-- | Generalization of 'Data.SBV.Control.getUIFunCVAssoc'
getUIFunCVAssoc :: forall m. (MonadIO m, MonadQuery m) => Maybe Int -> (String, SBVType) -> m ([([CV], CV)], CV)
getUIFunCVAssoc mbi (nm, typ) = do
  let modelIndex = case mbi of
                     Nothing -> ""
                     Just i  -> " :model_index " ++ show i

      cmd        = "(get-value (" ++ nm ++ ")" ++ modelIndex ++ ")"

      bad        = unexpected "get-value" cmd "a function value" Nothing

  r <- ask cmd

  let (ats, rt) = case typ of
                    SBVType as | length as > 1 -> (init as, last as)
                    _                          -> error $ "Data.SBV.getUIFunCVAssoc: Expected a function type, got: " ++ show typ

  let convert (vs, d) = (,) <$> mapM toPoint vs <*> toRes d
      toPoint (as, v)
         | length as == length ats = (,) <$> zipWithM recoverKindedValue ats as <*> toRes v
         | True                    = error $ "Data.SBV.getUIFunCVAssoc: Mismatching type/value arity, got: " ++ show (as, ats)

      toRes :: SExpr -> Maybe CV
      toRes = recoverKindedValue rt

      -- In case we end up in the pointwise scenario, boolify the result
      -- as that's the only type we support here.
      tryPointWise bailOut = do mbSExprs <- pointWiseExtract nm typ
                                case mbSExprs of
                                  Nothing     -> bailOut
                                  Just sExprs -> maybe bailOut return (convert sExprs)

  parse r bad $ \case EApp [EApp [ECon o, e]] | o == nm -> let bailOut = bad r Nothing
                                                           in case parseSExprFunction e of
                                                                Just (Right assocs) | Just res <- convert assocs                   -> return res
                                                                                    | True                                         -> tryPointWise bailOut

                                                                Just (Left nm')     | nm == nm', Just res <- defaultKindedValue rt -> return ([], res)
                                                                                    | True                                         -> bad r Nothing

                                                                Nothing                                                            -> tryPointWise bailOut

                      _                                 -> bad r Nothing

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

                       -- query for the precision if supported
                       let getPrecision = do cfg <- getConfig
                                             case supportsDeltaSat (capabilities (solver cfg)) of
                                               Nothing -> pure Nothing
                                               Just o  -> Just <$> ask o

                       parse r bad $ \case ECon "sat"       -> return Sat
                                           ECon "unsat"     -> return Unsat
                                           ECon "unknown"   -> return Unk
                                           ECon "delta-sat" -> DSat <$> getPrecision
                                           _                -> bad r Nothing

-- | What are the top level inputs? Trackers are returned as top level existentials
getQuantifiedInputs :: (MonadIO m, MonadQuery m) => m UserInputs
getQuantifiedInputs = do State{rinps} <- queryState
                         (rQinps, rTrackers) <- liftIO $ getInputs <$> readIORef rinps

                         let trackers = (EX,) <$> rTrackers
                             -- separate the existential prefix, which will go first
                             (preQs, postQs) = S.spanl (\(q, _) -> q == EX) rQinps

                         return $ preQs <> trackers <> postQs

-- | Get observables, i.e., those explicitly labeled by the user with a call to 'Data.SBV.observe'.
getObservables :: (MonadIO m, MonadQuery m) => m [(Name, CV)]
getObservables = do State{rObservables} <- queryState

                    rObs <- liftIO $ readIORef rObservables

                    -- This intentionally reverses the result; since 'rObs' stores in reversed order
                    let walk []             !sofar = return sofar
                        walk ((n, f, s):os) !sofar = do cv <- getValueCV Nothing s
                                                        if f cv
                                                          then walk os ((n, cv) : sofar)
                                                          else walk os            sofar

                    walk (F.toList rObs) []

-- | Get UIs, both constants and functions. This call returns both the before and after query ones.
-- Generalization of 'Data.SBV.Control.getUIs'. Note that if we have an defined axiom, then it
-- is not really a UI, so we drop those.
getUIs :: forall m. (MonadIO m, MonadQuery m) => m [(String, SBVType)]
getUIs = do State{rUIMap, raxioms, rIncState} <- queryState
            -- NB. no need to worry about new-defines, because we don't allow definitions once query mode starts
            defines <- do allAxs <- io $ readIORef raxioms
                          pure [nm | (True, nm, _) <- allAxs]

            prior <- io $ readIORef rUIMap
            new   <- io $ readIORef rIncState >>= readIORef . rNewUIs
            return $ nub $ sort [p | p@(n, _) <- Map.toList prior ++ Map.toList new, n `notElem` defines]

-- | Return all satisfying models.
getAllSatResult :: forall m. (MonadIO m, MonadQuery m, SolverContext m) => m AllSatResult
getAllSatResult = do queryDebug ["*** Checking Satisfiability, all solutions.."]

                     cfg <- getConfig
                     unless (supportsCustomQueries (capabilities (solver cfg))) $
                        error $ unlines [ ""
                                        , "*** Data.SBV: Backend solver " ++ show (name (solver cfg)) ++ " does not support custom queries."
                                        , "***"
                                        , "*** Custom query support is needed for allSat functionality."
                                        , "*** Please use a solver that supports this feature."
                                        ]

                     topState@State{rUsedKinds} <- queryState

                     ki    <- liftIO $ readIORef rUsedKinds
                     qinps <- getQuantifiedInputs

                     allUninterpreteds <- getUIs

                      -- Functions have at least two kinds in their type and all components must be "interpreted"
                     let allUiFuns = [u | satTrackUFs cfg                                         -- config says consider UIFs
                                        , u@(nm, SBVType as) <- allUninterpreteds, length as > 1  -- get the function ones
                                        , not (isNonModelVar cfg nm)                              -- make sure they aren't explicitly ignored
                                     ]

                         allUiRegs = [u | u@(nm, SBVType as) <- allUninterpreteds, length as == 1  -- non-function ones
                                        , not (isNonModelVar cfg nm)                               -- make sure not ignored
                                     ]

                         -- We can only "allSat" if all component types themselves are interpreted. (Otherwise
                         -- there is no way to reflect back the values to the solver.)
                         collectAcceptable []                           sofar = return sofar
                         collectAcceptable ((nm, t@(SBVType ats)):rest) sofar
                           | not (any hasUninterpretedSorts ats)
                           = collectAcceptable rest (nm : sofar)
                           | True
                           = do queryDebug [ "*** SBV.allSat: Uninterpreted function: " ++ nm ++ " :: " ++ show t
                                           , "*** Will *not* be used in allSat considerations since its type"
                                           , "*** has uninterpreted sorts present."
                                           ]
                                collectAcceptable rest sofar

                     uiFuns <- reverse <$> collectAcceptable allUiFuns []
                     _      <- collectAcceptable allUiRegs [] -- only done to get the queryDebug output. Actual result not needed/used

                     -- If there are uninterpreted functions, arrange so that z3's pretty-printer flattens things out
                     -- as cex's tend to get larger
                     unless (null uiFuns) $
                        let solverCaps = capabilities (solver cfg)
                        in case supportsFlattenedModels solverCaps of
                             Nothing   -> return ()
                             Just cmds -> mapM_ (send True) cmds

                     let usorts = [s | us@(KUserSort s _) <- Set.toAscList ki, isFree us]

                     unless (null usorts) $ queryDebug [ "*** SBV.allSat: Uninterpreted sorts present: " ++ unwords usorts
                                                       , "***             SBV will use equivalence classes to generate all-satisfying instances."
                                                       ]

                     let allModelInputs  = prefixExistentials qinps
                         -- Add on observables only if we're not in a quantified context:
                         hasQuantifiers  = S.length allModelInputs /= S.length qinps -- i.e., we dropped something
                         grabObservables = not hasQuantifiers

                         vars :: S.Seq (SVal, NamedSymVar)
                         vars = let mkSVal :: NamedSymVar -> (SVal, NamedSymVar)
                                    mkSVal nm@(getSV -> sv) = (SVal (kindOf sv) (Right (cache (const (return sv)))), nm)

                                    ignored n = isNonModelVar cfg (T.unpack n) || "__internal_sbv" `T.isPrefixOf` n

                                in fmap (mkSVal . namedSymVar)
                                   . S.filter (not . ignored . getUserName . namedSymVar)
                                   $ allModelInputs

                         -- If we have any universals, then the solutions are unique upto prefix existentials.
                         w = ALL `elem` F.toList (quantifier <$> qinps)


                     -- We can go fast using the disjoint model trick if things are simple enough:
                     --     - No quantifiers
                     --     - No uninterpreted functions (uninterpreted values are OK)
                     --     - No uninterpreted sorts
                     --
                     -- Why can't we support the above?
                     --     - Uninterpreted functions: There is no (standard) way to define a function as a literal in SMTLib.
                     --     Some solvers support lambda, but this isn't common/reliable yet.
                     --     - Uninterpreted sort: There's no way to access the value the solver assigns to an uninterpreted sort.
                     --
                     -- So, if these two things are present, we go the "slow" route, by repeatedly rejecting the
                     -- previous model and asking for a new one. If they don't exist (which is the common case anyhow)
                     -- we use an idea due to z3 folks <http://theory.stanford.edu/%7Enikolaj/programmingz3.html#sec-blocking-evaluations>
                     -- which splits the search space into disjoint models and can produce results much more quickly.
                     let isSimple = null allUiFuns && null usorts && not hasQuantifiers

                         start = AllSatResult { allSatMaxModelCountReached  = False
                                              , allSatHasPrefixExistentials = w
                                              , allSatSolverReturnedUnknown = False
                                              , allSatSolverReturnedDSat    = False
                                              , allSatResults               = []
                                              }

                     if isSimple
                        then do let mkVar :: (String, SBVType) -> IO (SVal, NamedSymVar)
                                    mkVar (nm, SBVType [k]) = do sv <- newExpr topState k (SBVApp (Uninterpreted nm) [])
                                                                 let sval = SVal k $ Right $ cache $ \_ -> pure sv
                                                                     nsv  = NamedSymVar sv (T.pack nm)
                                                                 pure (sval, nsv)
                                    mkVar nmt = error $ "Data.SBV: Impossible happened; allSat.mkVar. Unexpected: " ++ show nmt
                                uiVars <- io $ S.fromList <$> mapM mkVar allUiRegs
                                fastAllSat grabObservables                                        qinps (uiVars S.>< vars) cfg start
                        else    loop       grabObservables topState (allUiFuns, uiFuns) allUiRegs qinps              vars  cfg start

   where isFree (KUserSort _ Nothing) = True
         isFree _                     = False

         finalize cnt cfg sofar extra
                = when (allSatPrintAlong cfg && not (null (allSatResults sofar))) $ do
                           let msg 0 = "No solutions found."
                               msg 1 = "This is the only solution."
                               msg n = "Found " ++ show n ++ " different solutions."
                           io . putStrLn $ msg (cnt - 1)
                           case extra of
                             Nothing -> pure ()
                             Just m  -> io $ putStrLn m

         fastAllSat :: Bool -> S.Seq (Quantifier, NamedSymVar) -> S.Seq (SVal, NamedSymVar) -> SMTConfig -> AllSatResult -> m AllSatResult
         fastAllSat grabObservables qinps vars cfg start = do
                result <- io $ newIORef (0, start, False, Nothing)
                go result vars
                (found, sofar, _, extra) <- io $ readIORef result
                finalize (found+1) cfg sofar extra
                pure sofar

           where haveEnough have = case allSatMaxModelCount cfg of
                                     Just maxModels -> have >= maxModels
                                     _              -> False

                 go :: IORef (Int, AllSatResult, Bool, Maybe String) -> S.Seq (SVal, NamedSymVar) -> m ()
                 go finalResult = walk True
                   where shouldContinue = do (have, _, exitLoop, _) <- io $ readIORef finalResult
                                             pure $ not (exitLoop || haveEnough have)

                         walk :: Bool -> S.Seq (SVal, NamedSymVar) -> m ()
                         walk firstRun terms
                           | not firstRun && S.null terms
                           = pure ()
                           | True
                           = do mbCont <- do (have, sofar, exitLoop, _) <- io $ readIORef finalResult
                                             if exitLoop
                                                then pure Nothing
                                                else case allSatMaxModelCount cfg of
                                                       Just maxModels
                                                         | have >= maxModels -> do unless (allSatMaxModelCountReached sofar) $ do
                                                                                      queryDebug ["*** Maximum model count request of " ++ show maxModels ++ " reached, stopping the search."]
                                                                                      when (allSatPrintAlong cfg) $ io $ putStrLn "Search stopped since model count request was reached."
                                                                                      io $ modifyIORef' finalResult $ \(h, s, _, m) -> (h, s{ allSatMaxModelCountReached = True }, True, m)
                                                                                   pure Nothing
                                                       _                     -> pure $ Just $ have+1

                                case mbCont of
                                  Nothing  -> pure ()
                                  Just cnt -> do
                                    queryDebug ["Fast allSat, Looking for solution " ++ show cnt]

                                    cs <- checkSat

                                    case cs of
                                      Unsat  -> pure ()

                                      Unk    -> do let m = "Solver returned unknown, terminating query."
                                                   queryDebug ["*** " ++ m]
                                                   io $ modifyIORef' finalResult $ \(h, s, _, _) -> (h, s{allSatSolverReturnedUnknown = True}, True, Just ("[" ++ m ++ "]"))

                                      DSat _ -> do let m = "Solver returned delta-sat, terminating query."
                                                   queryDebug ["*** " ++ m]
                                                   io $ modifyIORef' finalResult $ \(h, s, _, _) -> (h, s{allSatSolverReturnedDSat = True}, True, Just ("[" ++ m ++ "]"))

                                      Sat    -> do assocs <- mapM (\(sval, NamedSymVar sv n) -> do !cv <- getValueCV Nothing sv
                                                                                                   return (sv, (n, (sval, cv)))) vars

                                                   bindings <- let grab i@(ALL, _)          = return (i, Nothing)
                                                                   grab i@(EX, getSV -> sv) = case lookupInput fst sv assocs of
                                                                                                Just (_, (_, (_, cv))) -> return (i, Just cv)
                                                                                                Nothing                -> do !cv <- getValueCV Nothing sv
                                                                                                                             return (i, Just cv)
                                                               in if validationRequested cfg
                                                                  then Just <$> mapM grab qinps
                                                                  else return Nothing

                                                   -- Add on observables if we're asked to do so:
                                                   obsvs <- if grabObservables
                                                               then getObservables
                                                               else do queryDebug ["*** In a quantified context, observables will not be printed."]
                                                                       return mempty

                                                   let lassocs = F.toList assocs
                                                       model   = SMTModel { modelObjectives = []
                                                                          , modelBindings   = F.toList <$> bindings
                                                                          , modelAssocs     =    (first T.unpack <$> sortOn fst obsvs)
                                                                                              <> [(T.unpack n, cv) | (_, (n, (_, cv))) <- lassocs]
                                                                          , modelUIFuns     = []
                                                                          }
                                                       currentResult = Satisfiable cfg model

                                                   io $ modifyIORef' finalResult $ \(h, s, e, m) -> let h' = h+1 in h' `seq` (h', s{allSatResults = currentResult : allSatResults s}, e, m)

                                                   when (allSatPrintAlong cfg) $ do
                                                        io $ putStrLn $ "Solution #" ++ show cnt ++ ":"
                                                        io $ putStrLn $ showModel cfg model

                                                   let findVal :: (SVal, NamedSymVar) -> (SVal, CV)
                                                       findVal (_, NamedSymVar sv nm) = case F.toList (S.filter (\(sv', _) -> sv == sv') assocs) of
                                                                                           [(_, (_, scv))] -> scv
                                                                                           _               -> error $ "Data.SBV: Cannot uniquely determine " ++ show nm ++ " in " ++ show assocs

                                                       cstr :: Bool -> (SVal, CV) -> m ()
                                                       cstr shouldReject (sv, cv) = constrain $ SBV $ mkEq (kindOf sv) sv (SVal (kindOf sv) (Left cv))
                                                         where mkEq :: Kind -> SVal -> SVal -> SVal
                                                               mkEq k a b
                                                                | isDouble k || isFloat k || isFP k
                                                                = if shouldReject
                                                                     then svNot  (a `fpEq` b)
                                                                     else         a `fpEq` b
                                                                | True
                                                                = if shouldReject
                                                                     then a `svNotEqual` b
                                                                     else a `svEqual`    b

                                                               fpEq a b = SVal KBool $ Right $ cache r
                                                                   where r st = do sva <- svToSV st a
                                                                                   svb <- svToSV st b
                                                                                   newExpr st KBool (SBVApp (IEEEFP FP_ObjEqual) [sva, svb])

                                                       reject, accept :: (SVal, NamedSymVar) -> m ()
                                                       reject = cstr True  . findVal
                                                       accept = cstr False . findVal

                                                       scope :: (SVal, NamedSymVar) -> S.Seq (SVal, NamedSymVar) -> m () -> m ()
                                                       scope cur pres c = do
                                                                send True "(push 1)"
                                                                reject cur
                                                                mapM_ accept pres
                                                                r <- c
                                                                send True "(pop 1)"
                                                                pure r

                                                   forM_ [0 .. length terms - 1] $ \i -> do
                                                        sc <- shouldContinue
                                                        when sc $ do case S.splitAt i terms of
                                                                       (pre, rest@(cur S.:<| _)) -> scope cur pre $ walk False rest
                                                                       _                         -> error "Data.SBV.allSat: Impossible happened, ran out of terms!"

         -- All sat loop. This is slower, as it implements the reject-the-previous model and loop around logic. But
         -- it can handle uninterpreted sorts; so we keep it here as a fall-back.
         loop grabObservables topState (allUiFuns, uiFunsToReject) allUiRegs qinps vars cfg = go (1::Int)
           where go :: Int -> AllSatResult -> m AllSatResult
                 go !cnt !sofar
                   | Just maxModels <- allSatMaxModelCount cfg, cnt > maxModels
                   = do queryDebug ["*** Maximum model count request of " ++ show maxModels ++ " reached, stopping the search."]
                        when (allSatPrintAlong cfg) $ io $ putStrLn "Search stopped since model count request was reached."
                        return $! sofar { allSatMaxModelCountReached = True }
                   | True
                   = do queryDebug ["Looking for solution " ++ show cnt]

                        cs <- checkSat

                        let endMsg = finalize cnt cfg sofar

                        case cs of
                          Unsat  -> do endMsg Nothing
                                       return sofar

                          Unk    -> do let m = "Solver returned unknown, terminating query."
                                       queryDebug ["*** " ++ m]
                                       endMsg $ Just $ "[" ++ m ++ "]"
                                       return sofar{ allSatSolverReturnedUnknown = True }

                          DSat _ -> do let m = "Solver returned delta-sat, terminating query."
                                       queryDebug ["*** " ++ m]
                                       endMsg $ Just $ "[" ++ m ++ "]"
                                       return sofar{ allSatSolverReturnedDSat = True }

                          Sat    -> do assocs <- mapM (\(sval, NamedSymVar sv n) -> do !cv <- getValueCV Nothing sv
                                                                                       return (sv, (n, (sval, cv)))) vars

                                       let getUIFun ui@(nm, t) = do cvs <- getUIFunCVAssoc Nothing ui
                                                                    return (nm, (t, cvs))
                                       uiFunVals <- mapM getUIFun allUiFuns

                                       uiRegVals <- mapM (\ui@(nm, _) -> (nm,) <$> getUICVal Nothing ui) allUiRegs

                                       -- Add on observables if we're asked to do so:
                                       obsvs <- if grabObservables
                                                   then getObservables
                                                   else do queryDebug ["*** In a quantified context, observables will not be printed."]
                                                           return mempty

                                       bindings <- let grab i@(ALL, _)          = return (i, Nothing)
                                                       grab i@(EX, getSV -> sv) = case lookupInput fst sv assocs of
                                                                                Just (_, (_, (_, cv))) -> return (i, Just cv)
                                                                                Nothing                -> do !cv <- getValueCV Nothing sv
                                                                                                             return (i, Just cv)
                                                   in if validationRequested cfg
                                                         then Just <$> mapM grab qinps
                                                         else return Nothing

                                       let model = SMTModel { modelObjectives = []
                                                            , modelBindings   = F.toList <$> bindings
                                                            , modelAssocs     =    uiRegVals
                                                                                <> (first T.unpack <$> sortOn fst obsvs)
                                                                                <> [(T.unpack n, cv) | (_, (n, (_, cv))) <- F.toList assocs]
                                                            , modelUIFuns     = uiFunVals
                                                            }
                                           m = Satisfiable cfg model

                                           (interpreteds, uninterpreteds) = S.partition (not . isFree . kindOf . fst) (fmap (snd . snd) assocs)

                                           interpretedRegUis = filter (not . isFree . kindOf . snd) uiRegVals

                                           interpretedRegUiSVs = [(cvt n (kindOf cv), cv) | (n, cv) <- interpretedRegUis]
                                             where cvt :: String -> Kind -> SVal
                                                   cvt nm k = SVal k $ Right $ cache r
                                                     where r st = newExpr st k (SBVApp (Uninterpreted nm) [])

                                           -- For each interpreted variable, figure out the model equivalence
                                           -- NB. When the kind is floating, we *have* to be careful, since +/- zero, and NaN's
                                           -- and equality don't get along!
                                           interpretedEqs :: [SVal]
                                           interpretedEqs = [mkNotEq (kindOf sv) sv (SVal (kindOf sv) (Left cv)) | (sv, cv) <- interpretedRegUiSVs <> F.toList interpreteds]
                                              where mkNotEq k a b
                                                     | isDouble k || isFloat k || isFP k
                                                     = svNot (a `fpEq` b)
                                                     | True
                                                     = a `svNotEqual` b

                                                    fpEq a b = SVal KBool $ Right $ cache r
                                                        where r st = do sva <- svToSV st a
                                                                        svb <- svToSV st b
                                                                        newExpr st KBool (SBVApp (IEEEFP FP_ObjEqual) [sva, svb])

                                           -- For each uninterpreted constant, use equivalence class
                                           uninterpretedEqs :: [SVal]
                                           uninterpretedEqs = concatMap pwDistinct         -- Assert that they are pairwise distinct
                                                            . filter (\l -> length l > 1)  -- Only need this class if it has at least two members
                                                            . map (map fst)                -- throw away values, we only need svals
                                                            . groupBy ((==) `on` snd)      -- make sure they belong to the same sort and have the same value
                                                            . sortOn snd                   -- sort them according to their CV (i.e., sort/value)
                                                            $ F.toList uninterpreteds
                                             where pwDistinct :: [SVal] -> [SVal]
                                                   pwDistinct ss = [x `svNotEqual` y | (x:ys) <- tails ss, y <- ys]

                                           -- For each uninterpreted function, create a disqualifying equation
                                           -- We do this rather brute-force, since we need to create a new function
                                           -- and do an existential assertion.
                                           uninterpretedReject :: Maybe [String]
                                           uninterpretedFuns   :: [String]
                                           (uninterpretedReject, uninterpretedFuns) = (uiReject, concat defs)
                                               where uiReject = case rejects of
                                                                  []  -> Nothing
                                                                  xs  -> Just xs

                                                     (rejects, defs) = unzip [mkNotEq ui | ui@(nm, _) <- uiFunVals, nm `elem` uiFunsToReject]

                                                     -- Otherwise, we have things to refute, go for it:
                                                     mkNotEq (nm, (SBVType ts, vs)) = (reject, def ++ dif)
                                                       where nm' = nm ++ "_model" ++ show cnt

                                                             reject = nm' ++ "_reject"

                                                             -- rounding mode doesn't matter here, just pick one
                                                             scv = cvToSMTLib RoundNearestTiesToEven

                                                             (ats, rt) = (init ts, last ts)

                                                             args = unwords ["(x!" ++ show i ++ " " ++ smtType t ++ ")" | (t, i) <- zip ats [(0::Int)..]]
                                                             res  = smtType rt

                                                             params = ["x!" ++ show i | (_, i) <- zip ats [(0::Int)..]]

                                                             uparams = unwords params

                                                             chain (vals, fallThru) = walk vals
                                                               where walk []               = ["   " ++ scv fallThru ++ replicate (length vals) ')']
                                                                     walk ((as, r) : rest) = ("   (ite " ++ cond as ++ " " ++ scv r ++ "") :  walk rest

                                                                     cond as = "(and " ++ unwords (zipWith eq params as) ++ ")"
                                                                     eq p a  = "(= " ++ p ++ " " ++ scv a ++ ")"

                                                             def =    ("(define-fun " ++ nm' ++ " (" ++ args ++ ") " ++ res)
                                                                   :  chain vs
                                                                   ++ [")"]

                                                             pad = replicate (1 + length nm' - length nm) ' '

                                                             dif = [ "(define-fun " ++  reject ++ " () Bool"
                                                                   , "   (exists (" ++ args ++ ")"
                                                                   , "           (distinct (" ++ nm  ++ pad ++ uparams ++ ")"
                                                                   , "                     (" ++ nm' ++ " " ++ uparams ++ "))))"
                                                                   ]

                                           eqs = interpretedEqs ++ uninterpretedEqs

                                           disallow = case eqs of
                                                        [] -> Nothing
                                                        _  -> Just $ SBV $ foldr1 svOr eqs

                                       when (allSatPrintAlong cfg) $ do
                                         io $ putStrLn $ "Solution #" ++ show cnt ++ ":"
                                         io $ putStrLn $ showModel cfg model

                                       let resultsSoFar = sofar { allSatResults = m : allSatResults sofar }

                                           -- This is clunky, but let's not generate a rejector unless we really need it
                                           needMoreIterations
                                                 | Just maxModels <- allSatMaxModelCount cfg, (cnt+1) > maxModels = False
                                                 | True                                                           = True

                                       -- Send function disequalities, if any:
                                       if not needMoreIterations
                                          then go (cnt+1) resultsSoFar
                                          else do let uiFunRejector   = "uiFunRejector_model_" ++ show cnt
                                                      header          = "define-fun " ++ uiFunRejector ++ " () Bool "

                                                      defineRejector []     = return ()
                                                      defineRejector [x]    = send True $ "(" ++ header ++ x ++ ")"
                                                      defineRejector (x:xs) = mapM_ (send True) $ mergeSExpr $  ("(" ++ header)
                                                                                                             :  ("        (or " ++ x)
                                                                                                             :  ["            " ++ e | e <- xs]
                                                                                                             ++ ["        ))"]
                                                  rejectFuncs <- case uninterpretedReject of
                                                                   Nothing -> return Nothing
                                                                   Just fs -> do mapM_ (send True) $ mergeSExpr uninterpretedFuns
                                                                                 defineRejector fs
                                                                                 return $ Just uiFunRejector

                                                  -- send the disallow clause and the uninterpreted rejector:
                                                  case (disallow, rejectFuncs) of
                                                     (Nothing, Nothing) -> pure resultsSoFar
                                                     (Just d,  Nothing) -> do constrain d
                                                                              go (cnt+1) resultsSoFar
                                                     (Nothing, Just f)  -> do send True $ "(assert " ++ f ++ ")"
                                                                              go (cnt+1) resultsSoFar
                                                     (Just d,  Just f)  -> -- This is where it gets ugly. We have an SBV and a string and we need to "or" them.
                                                                           -- But we need a way to force 'd' to be produced. So, go ahead and force it:
                                                                           do constrain $ d .=> d  -- NB: Redundant, but it makes sure the corresponding constraint gets shown
                                                                              svd <- io $ svToSV topState (unSBV d)
                                                                              send True $ "(assert (or " ++ f ++ " " ++ show svd ++ "))"
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
                                              SMTMode _ stage s c -> (c, s, isSafetyCheckingIStage stage, isSetupIStage stage)
                                              _                   -> error $ "runProofOn: Unexpected run mode: " ++ show rm

         flipQ (ALL, x) = (EX,  x)
         flipQ (EX,  x) = (ALL, x)

         skolemize :: [(Quantifier, NamedSymVar)] -> [Either SV (SV, [SV])]
         skolemize quants = go quants ([], [])
           where go []                        (_,  sofar) = reverse sofar
                 go ((ALL, getSV -> v) :rest) (us, sofar) = go rest (v:us, Left v : sofar)
                 go ((EX,  getSV -> v) :rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)

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

     -- Make sure the phases match:
     () <- liftIO $ case (queryContext, rm) of
                      (QueryInternal, _)                                -> return ()  -- no worries, internal
                      (QueryExternal, SMTMode QueryExternal ISetup _ _) -> return () -- legitimate runSMT call
                      _                                                 -> invalidQuery rm

     -- If we're doing an external query, then we cannot allow quantifiers to be present. Why?
     -- Consider:
     --
     --      issue = do x :: SBool <- sbvForall_
     --                 y :: SBool <- sbvExists_
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
     --
     -- However, as discussed in <https://github.com/LeventErkok/sbv/issues/459>, we'll allow for this
     -- if the user explicitly asks as to do so. In that case, all bets are off!

     let allowQQs = case rm of
                      SMTMode _ _ _ cfg -> allowQuantifiedQueries cfg
                      CodeGen           -> False -- doesn't matter in these two
                      Concrete{}        -> False -- cases, but we're being careful

     () <- unless allowQQs $ liftIO $
                    case queryContext of
                      QueryInternal -> return ()         -- we're good, internal usages don't mess with scopes
                      QueryExternal -> do
                        userInps  <- userInputsToList . userInputs <$> readIORef (rinps st)
                        let badInps = reverse [n | (ALL, getUserName' -> n) <- userInps]
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
        SMTMode qc stage isSAT cfg | not (isRunIStage stage) -> do

                  let slvr    = solver cfg
                      backend = engine slvr

                  -- make sure if we have dsat precision, then solver supports it
                  let dsatOK =  isNothing (dsatPrecision cfg)
                             || isJust    (supportsDeltaSat (capabilities slvr))

                  unless dsatOK $ error $ unlines
                                     [ ""
                                     , "*** Data.SBV: Delta-sat precision is specified."
                                     , "***           But the chosen solver (" ++ show (name slvr) ++ ") does not support"
                                     , "***           delta-satisfiability."
                                     ]

                  res     <- liftIO $ extractSymbolicSimulationState st
                  setOpts <- liftIO $ reverse <$> readIORef (rSMTOptions st)

                  let SMTProblem{smtLibPgm} = runProofOn rm queryContext [] res
                      cfg' = cfg { solverSetOptions = solverSetOptions cfg ++ setOpts }
                      pgm  = smtLibPgm cfg'

                  liftIO $ writeIORef (runMode st) $ SMTMode qc IRun isSAT cfg

                  lift $ join $ liftIO $ backend cfg' st (show pgm) $ extractIO . runReaderT userQuery

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
        --        -- constrain $ a .> literal av + 1      -- Can't do this since we're "out" of query. Sigh.
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

        SMTMode _ IRun _ _ -> error $ unlines [ ""
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
        _ -> invalidQuery rm

  where invalidQuery rm = error $ unlines [ ""
                                          , "*** Data.SBV: Invalid query call."
                                          , "***"
                                          , "***   Current mode: " ++ show rm
                                          , "***"
                                          , "*** Query calls are only valid within runSMT/runSMTWith calls,"
                                          , "*** and each call to runSMT should have only one query call inside."
                                          ]

{-# ANN module          ("HLint: ignore Reduce duplication" :: String) #-}
{-# ANN getAllSatResult ("HLint: ignore Use forM_"          :: String) #-}
