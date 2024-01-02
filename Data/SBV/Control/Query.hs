-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Control.Query
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Querying a solver interactively.
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Control.Query (
       send, ask, retrieveResponse
     , CheckSatResult(..), checkSat, checkSatUsing, checkSatAssuming, checkSatAssumingWithUnsatisfiableSet
     , getUnsatCore, getProof, getInterpolantMathSAT, getInterpolantZ3, getAbduct, getAbductNext, getAssignment, getOption
     , freshVar, freshVar_, freshArray, freshArray_, freshLambdaArray, freshLambdaArray_
     , push, pop, getAssertionStackDepth
     , inNewAssertionStack, echo, caseSplit, resetAssertions, exit, getAssertions, getValue, getUninterpretedValue, getModel, getSMTResult
     , getLexicographicOptResults, getIndependentOptResults, getParetoOptResults, getAllSatResult, getUnknownReason, getObservables, ensureSat
     , SMTOption(..), SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..), getInfo
     , Logic(..), Assignment(..)
     , ignoreExitCode, timeout
     , (|->)
     , mkSMTResult
     , io
     ) where

import Control.Monad          (unless, when, zipWithM)
import Control.Monad.IO.Class (MonadIO)

import Data.IORef (readIORef)

import qualified Data.Map.Strict    as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Sequence      as S
import qualified Data.Text          as T
import qualified Data.Foldable      as F


import Data.Char      (toLower)
import Data.List      (intercalate, nubBy, sortOn)
import Data.Maybe     (listToMaybe, catMaybes, fromMaybe)
import Data.Function  (on)
import Data.Bifunctor (first)
import Data.Foldable  (toList)

import Data.SBV.Core.Data

import Data.SBV.Core.Symbolic (MonadQuery(..), State(..), incrementInternalCounter, validationRequested, getSV, lookupInput, mustIgnoreVar)

import Data.SBV.Utils.SExpr

import Data.SBV.Control.Types
import Data.SBV.Control.Utils

import Data.SBV.Utils.PrettyNum (showNegativeNumber)

-- | An Assignment of a model binding
data Assignment = Assign SVal CV

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
stringsOf (ECon s)           = [s]
stringsOf (ENum (i, _))      = [show i]
stringsOf (EReal   r)        = [show r]
stringsOf (EFloat  f)        = [show f]
stringsOf (EFloatingPoint f) = [show f]
stringsOf (EDouble d)        = [show d]
stringsOf (EApp ss)          = concatMap stringsOf ss

-- Sort of a light-hearted show for SExprs, for better consumption at the user level.
serialize :: Bool -> SExpr -> String
serialize removeQuotes = go
  where go (ECon s)           = if removeQuotes then unQuote s else s
        go (ENum (i, _))      = showNegativeNumber i
        go (EReal   r)        = showNegativeNumber r
        go (EFloat  f)        = showNegativeNumber f
        go (EDouble d)        = showNegativeNumber d
        go (EFloatingPoint f) = show f
        go (EApp [x])         = go x
        go (EApp ss)          = "(" ++ unwords (map go ss) ++ ")"

-- | Generalization of 'Data.SBV.Control.getInfo'
getInfo :: (MonadIO m, MonadQuery m) => SMTInfoFlag -> m SMTInfoResponse
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

-- | Generalization of 'Data.SBV.Control.getInfo'
getOption :: (MonadIO m, MonadQuery m) => (a -> SMTOption) -> m (Maybe SMTOption)
getOption f = case f undefined of
                 DiagnosticOutputChannel{}   -> askFor "DiagnosticOutputChannel"   ":diagnostic-output-channel"   $ string     DiagnosticOutputChannel
                 ProduceAssertions{}         -> askFor "ProduceAssertions"         ":produce-assertions"          $ bool       ProduceAssertions
                 ProduceAssignments{}        -> askFor "ProduceAssignments"        ":produce-assignments"         $ bool       ProduceAssignments
                 ProduceProofs{}             -> askFor "ProduceProofs"             ":produce-proofs"              $ bool       ProduceProofs
                 ProduceInterpolants{}       -> askFor "ProduceInterpolants"       ":produce-interpolants"        $ bool       ProduceInterpolants
                 ProduceUnsatAssumptions{}   -> askFor "ProduceUnsatAssumptions"   ":produce-unsat-assumptions"   $ bool       ProduceUnsatAssumptions
                 ProduceUnsatCores{}         -> askFor "ProduceUnsatCores"         ":produce-unsat-cores"         $ bool       ProduceUnsatCores
                 ProduceAbducts{}            -> askFor "ProduceAbducts"            ":produce-abducts"             $ bool       ProduceAbducts
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

-- | Generalization of 'Data.SBV.Control.getUnknownReason'
getUnknownReason :: (MonadIO m, MonadQuery m) => m SMTReasonUnknown
getUnknownReason = do ru <- getInfo ReasonUnknown
                      case ru of
                        Resp_Unsupported     -> return $ UnknownOther "Solver responded: Unsupported."
                        Resp_ReasonUnknown r -> return r
                        -- Shouldn't happen, but just in case:
                        _                    -> error $ "Unexpected reason value received: " ++ show ru

-- | Generalization of 'Data.SBV.Control.ensureSat'
ensureSat :: (MonadIO m, MonadQuery m) => m ()
ensureSat = do cfg <- getConfig
               cs <- checkSatUsing $ satCmd cfg
               case cs of
                 Sat    -> return ()
                 DSat{} -> return ()
                 Unk    -> do s <- getUnknownReason
                              error $ unlines [ ""
                                              , "*** Data.SBV.ensureSat: Solver reported Unknown!"
                                              , "*** Reason: " ++ show s
                                              ]
                 Unsat  -> error "Data.SBV.ensureSat: Solver reported Unsat!"

-- | Generalization of 'Data.SBV.Control.getSMTResult'
getSMTResult :: (MonadIO m, MonadQuery m) => m SMTResult
getSMTResult = do cfg <- getConfig
                  cs  <- checkSat
                  case cs of
                    Unsat  -> Unsatisfiable cfg   <$> getUnsatCoreIfRequested
                    Sat    -> Satisfiable   cfg   <$> getModel
                    DSat p -> DeltaSat      cfg p <$> getModel
                    Unk    -> Unknown       cfg   <$> getUnknownReason

-- | Classify a model based on whether it has unbound objectives or not.
classifyModel :: SMTConfig -> SMTModel -> SMTResult
classifyModel cfg m
  | any isExt (modelObjectives m) = SatExtField cfg m
  | True                          = Satisfiable cfg m
  where isExt (_, v) = not $ isRegularCV v

-- | Generalization of 'Data.SBV.Control.getLexicographicOptResults'
getLexicographicOptResults :: (MonadIO m, MonadQuery m) => m SMTResult
getLexicographicOptResults = do cfg <- getConfig
                                cs  <- checkSat
                                case cs of
                                  Unsat  -> Unsatisfiable cfg <$> getUnsatCoreIfRequested
                                  Sat    -> classifyModel cfg <$> getModelWithObjectives
                                  DSat{} -> classifyModel cfg <$> getModelWithObjectives
                                  Unk    -> Unknown       cfg <$> getUnknownReason
   where getModelWithObjectives = do objectiveValues <- getObjectiveValues
                                     m               <- getModel
                                     return m {modelObjectives = objectiveValues}

-- | Generalization of 'Data.SBV.Control.getIndependentOptResults'
getIndependentOptResults :: forall m. (MonadIO m, MonadQuery m) => [String] -> m [(String, SMTResult)]
getIndependentOptResults objNames = do cfg <- getConfig
                                       cs  <- checkSat

                                       case cs of
                                         Unsat  -> getUnsatCoreIfRequested >>= \mbUC -> return [(nm, Unsatisfiable cfg mbUC) | nm <- objNames]
                                         Sat    -> continue (classifyModel cfg)
                                         DSat{} -> continue (classifyModel cfg)
                                         Unk    -> do ur <- Unknown cfg <$> getUnknownReason
                                                      return [(nm, ur) | nm <- objNames]

  where continue classify = do objectiveValues <- getObjectiveValues
                               nms <- zipWithM getIndependentResult [0..] objNames
                               return [(n, classify (m {modelObjectives = objectiveValues})) | (n, m) <- nms]

        getIndependentResult :: Int -> String -> m (String, SMTModel)
        getIndependentResult i s = do m <- getModelAtIndex (Just i)
                                      return (s, m)

-- | Generalization of 'Data.SBV.Control.getParetoOptResults'
getParetoOptResults :: (MonadIO m, MonadQuery m) => Maybe Int -> m (Bool, [SMTResult])
getParetoOptResults (Just i)
        | i <= 0             = return (True, [])
getParetoOptResults mbN      = do cfg <- getConfig
                                  cs  <- checkSat

                                  case cs of
                                    Unsat  -> return (False, [])
                                    Sat    -> continue (classifyModel cfg)
                                    DSat{} -> continue (classifyModel cfg)
                                    Unk    -> do ur <- getUnknownReason
                                                 return (False, [ProofError cfg [show ur] Nothing])

  where continue classify = do m <- getModel
                               (limReached, fronts) <- getParetoFronts (subtract 1 <$> mbN) [m]
                               return (limReached, reverse (map classify fronts))

        getParetoFronts :: (MonadIO m, MonadQuery m) => Maybe Int -> [SMTModel] -> m (Bool, [SMTModel])
        getParetoFronts (Just i) sofar | i <= 0 = return (True, sofar)
        getParetoFronts mbi      sofar          = do cs <- checkSat
                                                     let more = getModel >>= \m -> getParetoFronts (subtract 1 <$> mbi) (m : sofar)
                                                     case cs of
                                                       Unsat  -> return (False, sofar)
                                                       Sat    -> more
                                                       DSat{} -> more
                                                       Unk    -> more

-- | Generalization of 'Data.SBV.Control.getModel'
getModel :: (MonadIO m, MonadQuery m) => m SMTModel
getModel = getModelAtIndex Nothing

-- | Get a model stored at an index. This is likely very Z3 specific!
getModelAtIndex :: (MonadIO m, MonadQuery m) => Maybe Int -> m SMTModel
getModelAtIndex mbi = do
    State{runMode} <- queryState
    rm <- io $ readIORef runMode
    case rm of
      m@CodeGen     -> error $ "SBV.getModel: Model is not available in mode: " ++ show m
      m@LambdaGen{} -> error $ "SBV.getModel: Model is not available in mode: " ++ show m
      m@Concrete{}  -> error $ "SBV.getModel: Model is not available in mode: " ++ show m
      SMTMode{}     -> do
          cfg <- getConfig
          uis <- getUIs

          allModelInputs <- getTopLevelInputs
          obsvs          <- getObservables


          inputAssocs <- let grab (NamedSymVar sv nm) = let wrap !c = (sv, (nm, c)) in wrap <$> getValueCV mbi sv
                         in mapM grab allModelInputs

          let name     = fst . snd
              removeSV = snd
              prepare  = S.unstableSort . S.filter (not . mustIgnoreVar cfg . T.unpack . name)
              assocs   = S.fromList (sortOn fst obsvs) <> fmap removeSV (prepare inputAssocs)

          -- collect UIs, and UI functions if requested
          let uiFuns = [ui | ui@(nm, (_, _, SBVType as)) <- uis, length as >  1, allSatTrackUFs cfg, not (mustIgnoreVar cfg nm)] -- functions have at least two things in their type!
              uiRegs = [ui | ui@(nm, (_, _, SBVType as)) <- uis, length as == 1,                     not (mustIgnoreVar cfg nm)]

          -- If there are uninterpreted functions, arrange so that z3's pretty-printer flattens things out
          -- as cex's tend to get larger
          unless (null uiFuns) $
             let solverCaps = capabilities (solver cfg)
             in case supportsFlattenedModels solverCaps of
                  Nothing   -> return ()
                  Just cmds -> mapM_ (send True) cmds

          bindings <- let get i@(getSV -> sv) = case lookupInput fst sv inputAssocs of
                                                  Just (_, (_, cv)) -> return (i, cv)
                                                  Nothing           -> do cv <- getValueCV mbi sv
                                                                          return (i, cv)

                      in if validationRequested cfg
                         then Just <$> mapM get allModelInputs
                         else return Nothing

          uiFunVals <- mapM (\ui@(nm, (c, _, t)) -> (\a -> (nm, (c, t, a))) <$> getUIFunCVAssoc mbi ui) uiFuns

          uiVals    <- mapM (\ui@(nm, (_, _, _)) -> (nm,) <$> getUICVal mbi ui) uiRegs

          return SMTModel { modelObjectives = []
                          , modelBindings   = toList <$> bindings
                          , modelAssocs     = uiVals ++ toList (first T.unpack <$> assocs)
                          , modelUIFuns     = uiFunVals
                          }

-- | Just after a check-sat is issued, collect objective values. Used
-- internally only, not exposed to the user.
getObjectiveValues :: forall m. (MonadIO m, MonadQuery m) => m [(String, GeneralizedCV)]
getObjectiveValues = do let cmd = "(get-objectives)"

                            bad = unexpected "getObjectiveValues" cmd "a list of objective values" Nothing

                        r <- ask cmd

                        inputs <- F.toList <$> getTopLevelInputs

                        parse r bad $ \case EApp (ECon "objectives" : es) -> catMaybes <$> mapM (getObjValue (bad r) inputs) es
                                            _                             -> bad r Nothing

  where -- | Parse an objective value out.
        getObjValue :: (forall a. Maybe [String] -> m a) -> [NamedSymVar] -> SExpr -> m (Maybe (String, GeneralizedCV))
        getObjValue bailOut inputs expr =
                case expr of
                  EApp [_]          -> return Nothing            -- Happens when a soft-assertion has no associated group.
                  EApp [ECon nm, v] -> locate nm v               -- Regular case
                  _                 -> dontUnderstand (show expr)

          where locate nm v = case listToMaybe [p | p@(NamedSymVar sv _) <- inputs, show sv == nm] of
                                Nothing                          -> return Nothing -- Happens when the soft assertion has a group-id that's not one of the input names
                                Just (NamedSymVar sv actualName) -> grab sv v >>= \val -> return $ Just (T.unpack actualName, val)

                dontUnderstand s = bailOut $ Just [ "Unable to understand solver output."
                                                  , "While trying to process: " ++ s
                                                  ]

                grab :: SV -> SExpr -> m GeneralizedCV
                grab s topExpr
                  | Just v <- recoverKindedValue k topExpr = return $ RegularCV v
                  | True                                   = ExtendedCV <$> cvt (simplify topExpr)
                  where k = kindOf s

                        -- Convert to an extended expression. Hopefully complete!
                        cvt :: SExpr -> m ExtCV
                        cvt (ECon "oo")                    = return $ Infinite  k
                        cvt (ECon "epsilon")               = return $ Epsilon   k
                        cvt (EApp [ECon "interval", x, y]) =          Interval  <$> cvt x <*> cvt y
                        cvt (ENum    (i, _))               = return $ BoundedCV $ mkConstCV k i
                        cvt (EReal   r)                    = return $ BoundedCV $ CV k $ CAlgReal r
                        cvt (EFloat  f)                    = return $ BoundedCV $ CV k $ CFloat   f
                        cvt (EDouble d)                    = return $ BoundedCV $ CV k $ CDouble  d
                        cvt (EApp [ECon "+", x, y])        =          AddExtCV <$> cvt x <*> cvt y
                        cvt (EApp [ECon "*", x, y])        =          MulExtCV <$> cvt x <*> cvt y
                        -- Nothing else should show up, hopefully!
                        cvt e = dontUnderstand (show e)

                        -- drop the pesky to_real's that Z3 produces.. Cool but useless.
                        simplify :: SExpr -> SExpr
                        simplify (EApp [ECon "to_real", n]) = n
                        simplify (EApp xs)                  = EApp (map simplify xs)
                        simplify e                          = e

-- | Generalization of 'Data.SBV.Control.checkSatAssuming'
checkSatAssuming :: (MonadIO m, MonadQuery m) => [SBool] -> m CheckSatResult
checkSatAssuming sBools = fst <$> checkSatAssumingHelper False sBools

-- | Generalization of 'Data.SBV.Control.checkSatAssumingWithUnsatisfiableSet'
checkSatAssumingWithUnsatisfiableSet :: (MonadIO m, MonadQuery m) => [SBool] -> m (CheckSatResult, Maybe [SBool])
checkSatAssumingWithUnsatisfiableSet = checkSatAssumingHelper True

-- | Helper for the two variants of checkSatAssuming we have. Internal only.
checkSatAssumingHelper :: (MonadIO m, MonadQuery m) => Bool -> [SBool] -> m (CheckSatResult, Maybe [SBool])
checkSatAssumingHelper getAssumptions sBools = do
        -- sigh.. SMT-Lib requires the values to be literals only. So, create proxies.
        let mkAssumption st = do swsOriginal <- mapM (\sb -> do sv <- sbvToSV st sb
                                                                return (sv, sb)) sBools

                                 -- drop duplicates and trues
                                 let swbs = [p | p@(sv, _) <- nubBy ((==) `on` fst) swsOriginal, sv /= trueSV]

                                 -- get a unique proxy name for each
                                 uniqueSWBs <- mapM (\(sv, sb) -> do unique <- incrementInternalCounter st
                                                                     return (sv, (unique, sb))) swbs

                                 let translate (sv, (unique, sb)) = (nm, decls, (proxy, sb))
                                        where nm    = show sv
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

-- | Generalization of 'Data.SBV.Control.getAssertionStackDepth'
getAssertionStackDepth :: (MonadIO m, MonadQuery m) => m Int
getAssertionStackDepth = queryAssertionStackDepth <$> getQueryState

-- | Upon a pop, we need to restore all arrays and tables. See: http://github.com/LeventErkok/sbv/issues/374
restoreTablesAndArrays :: (MonadIO m, MonadQuery m) => m ()
restoreTablesAndArrays = do st <- queryState

                            tCount <- M.size  <$> (io . readIORef) (rtblMap   st)
                            aCount <- IM.size <$> (io . readIORef) (rArrayMap st)

                            let tInits = [ "table"  ++ show i ++ "_initializer" | i <- [0 .. tCount - 1]]
                                aInits = [ "array_" ++ show i ++ "_initializer" | i <- [0 .. aCount - 1]]
                                inits  = tInits ++ aInits

                            case inits of
                              []  -> return ()   -- Nothing to do
                              [x] -> send True $ "(assert " ++ x ++ ")"
                              xs  -> send True $ "(assert (and " ++ unwords xs ++ "))"

-- | Generalization of 'Data.SBV.Control.inNewAssertionStack'
inNewAssertionStack :: (MonadIO m, MonadQuery m) => m a -> m a
inNewAssertionStack q = do push 1
                           r <- q
                           pop 1
                           return r

-- | Generalization of 'Data.SBV.Control.push'
push :: (MonadIO m, MonadQuery m) => Int -> m ()
push i
 | i <= 0 = error $ "Data.SBV: push requires a strictly positive level argument, received: " ++ show i
 | True   = do depth <- getAssertionStackDepth
               send True $ "(push " ++ show i ++ ")"
               modifyQueryState $ \s -> s{queryAssertionStackDepth = depth + i}

-- | Generalization of 'Data.SBV.Control.pop'
pop :: (MonadIO m, MonadQuery m) => Int -> m ()
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

-- | Generalization of 'Data.SBV.Control.caseSplit'
caseSplit :: (MonadIO m, MonadQuery m) => Bool -> [(String, SBool)] -> m (Maybe (String, SMTResult))
caseSplit printCases cases = do cfg <- getConfig
                                go cfg (cases ++ [("Coverage", sNot (sOr (map snd cases)))])
  where msg = when printCases . io . putStrLn

        go _ []            = return Nothing
        go cfg ((n,c):ncs) = do let notify s = msg $ "Case " ++ n ++ ": " ++ s

                                notify "Starting"
                                r <- checkSatAssuming [c]

                                case r of
                                  Unsat    -> do notify "Unsatisfiable"
                                                 go cfg ncs

                                  Sat      -> do notify "Satisfiable"
                                                 res <- Satisfiable cfg <$> getModel
                                                 return $ Just (n, res)

                                  DSat mbP -> do notify $ "Delta satisfiable" ++ maybe "" (" (precision: " ++) mbP
                                                 res <- DeltaSat cfg mbP <$> getModel
                                                 return $ Just (n, res)

                                  Unk      -> do notify "Unknown"
                                                 res <- Unknown cfg <$> getUnknownReason
                                                 return $ Just (n, res)

-- | Generalization of 'Data.SBV.Control.resetAssertions'
resetAssertions :: (MonadIO m, MonadQuery m) => m ()
resetAssertions = do send True "(reset-assertions)"
                     modifyQueryState $ \s -> s{ queryAssertionStackDepth = 0 }

                     -- Make sure we restore tables and arrays after resetAssertions: See: https://github.com/LeventErkok/sbv/issues/535
                     restoreTablesAndArrays

-- | Generalization of 'Data.SBV.Control.echo'
echo :: (MonadIO m, MonadQuery m) => String -> m ()
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

-- | Generalization of 'Data.SBV.Control.exit'
exit :: (MonadIO m, MonadQuery m) => m ()
exit = do send True "(exit)"
          modifyQueryState $ \s -> s{queryAssertionStackDepth = 0}

-- | Generalization of 'Data.SBV.Control.getUnsatCore'
getUnsatCore :: (MonadIO m, MonadQuery m) => m [String]
getUnsatCore = do
        let cmd = "(get-unsat-core)"
            bad = unexpected "getUnsatCore" cmd "an unsat-core response"
                           $ Just [ "Make sure you use:"
                                  , ""
                                  , "       setOption $ ProduceUnsatCores True"
                                  , ""
                                  , "so the solver will be ready to compute unsat cores,"
                                  , "and that there is a model by first issuing a 'checkSat' call."
                                  , ""
                                  , "If using z3, you might also optionally want to set:"
                                  , ""
                                  , "       setOption $ OptionKeyword \":smt.core.minimize\" [\"true\"]"
                                  , ""
                                  , "to make sure the unsat core doesn't have irrelevant entries,"
                                  , "though this might incur a performance penalty."


                                  ]

        r <- ask cmd

        parse r bad $ \case
           EApp es | Just xs <- mapM fromECon es -> return $ map unBar xs
           _                                     -> bad r Nothing

-- | Retrieve the unsat core if it was asked for in the configuration
getUnsatCoreIfRequested :: (MonadIO m, MonadQuery m) => m (Maybe [String])
getUnsatCoreIfRequested = do
        cfg <- getConfig
        if or [b | ProduceUnsatCores b <- solverSetOptions cfg]
           then Just <$> getUnsatCore
           else return Nothing

-- | Generalization of 'Data.SBV.Control.getProof'
getProof :: (MonadIO m, MonadQuery m) => m String
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

-- | Generalization of 'Data.SBV.Control.getInterpolantMathSAT'. Use this version with MathSAT.
getInterpolantMathSAT :: (MonadIO m, MonadQuery m) => [String] -> m String
getInterpolantMathSAT fs
  | null fs
  = error "SBV.getInterpolantMathSAT requires at least one marked constraint, received none!"
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


-- | Generalization of 'Data.SBV.Control.getAbduct'.
getAbduct :: (SolverContext m, MonadIO m, MonadQuery m) => Maybe String -> String -> SBool -> m String
getAbduct mbGrammar defName b = do
   s <- inNewContext (`sbvToSV` b)
   let cmd = "(get-abduct " ++ defName ++ " " ++ show s ++ fromMaybe "" mbGrammar ++ ")"
       bad = unexpected "getAbduct" cmd "a get-abduct response" Nothing

   r <- ask cmd

   parse r bad $ \e -> return $ serialize False e

-- | Generalization of 'Data.SBV.Control.getAbductNext'.
getAbductNext :: (MonadIO m, MonadQuery m) => m String
getAbductNext = do
   let cmd = "(get-abduct-next)"
       bad = unexpected "getAbductNext" cmd "a get-abduct-next response" Nothing

   r <- ask cmd

   parse r bad $ \e -> return $ serialize False e

-- | Generalization of 'Data.SBV.Control.getInterpolantZ3'. Use this version with Z3.
getInterpolantZ3 :: (MonadIO m, MonadQuery m) => [SBool] -> m String
getInterpolantZ3 fs
  | length fs < 2
  = error $ "SBV.getInterpolantZ3 requires at least two booleans, received: " ++ show fs
  | True
  = do ss <- let fAll []     sofar = return $ reverse sofar
                 fAll (b:bs) sofar = do sv <- inNewContext (`sbvToSV` b)
                                        fAll bs (sv : sofar)
             in fAll fs []

       let cmd = "(get-interpolant " ++ unwords (map show ss) ++ ")"
           bad = unexpected "getInterpolant" cmd "a get-interpolant response" Nothing

       r <- ask cmd

       parse r bad $ \e -> return $ serialize False e

-- | Generalization of 'Data.SBV.Control.getAssertions'
getAssertions :: (MonadIO m, MonadQuery m) => m [String]
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

-- | Generalization of 'Data.SBV.Control.getAssignment'
getAssignment :: (MonadIO m, MonadQuery m) => m [(String, Bool)]
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
(|->) :: SymVal a => SBV a -> a -> Assignment
SBV a |-> v = case literal v of
                SBV (SVal _ (Left cv)) -> Assign a cv
                r                      -> error $ "Data.SBV: Impossible happened in |->: Cannot construct a CV with literal: " ++ show r

-- | Generalization of 'Data.SBV.Control.mkSMTResult'
-- NB. This function does not allow users to create interpretations for UI-Funs. But that's
-- probably not a good idea anyhow. Also, if you use the 'validateModel' or 'optimizeValidateConstraints' features, SBV will
-- fail on models returned via this function.
mkSMTResult :: (MonadIO m, MonadQuery m) => [Assignment] -> m SMTResult
mkSMTResult asgns = do
             QueryState{queryConfig} <- getQueryState
             inps <- F.toList <$> getTopLevelInputs

             let grabValues st = do let extract (Assign s n) = sbvToSV st (SBV s) >>= \sv -> return (sv, n)

                                    modelAssignment <- mapM extract asgns

                                    -- sanity checks
                                    --     - All existentials should be given a value
                                    --     - No duplicates
                                    --     - No bindings to vars that are not inputs
                                    let userSS = map fst modelAssignment

                                        missing, extra, dup :: [String]
                                        missing = [T.unpack n | NamedSymVar s n <- inps, s `notElem` userSS]
                                        extra   = [show s | s <- userSS, s `notElem` map getSV inps]
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

                                    let findName s = case [T.unpack nm | NamedSymVar i nm <- inps, s == i] of
                                                        [nm] -> nm
                                                        []   -> error "*** Data.SBV: Impossible happened: Cannot find " ++ show s ++ " in the input list"
                                                        nms  -> error $ unlines [ ""
                                                                                , "*** Data.SBV: Impossible happened: Multiple matches for: " ++ show s
                                                                                , "***   Candidates: " ++ unwords nms
                                                                                ]

                                    return [(findName s, n) | (s, n) <- modelAssignment]

             assocs <- inNewContext grabValues

             let m = SMTModel { modelObjectives = []
                              , modelBindings   = Nothing
                              , modelAssocs     = assocs
                              , modelUIFuns     = []
                              }

             return $ Satisfiable queryConfig m

{- HLint ignore getModelAtIndex "Use forM_" -}
