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
     , CheckSatResult(..), checkSat, checkSatUsing, checkSatAssuming, getUnsatCore, getProof, getAssignment, getOption
     , push, pop, getAssertionStackDepth, echo
     , resetAssertions, exit
     , getAssertions
     , getValue, getModel, getSMTResult, getSMTResultWithObjectives, getAllSatResult
     , SMTOption(..)
     , SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..), getInfo
     , Logic(..), Assignment(..)
     , ignoreExitCode, timeout
     , (|->)
     , mkResult
     , io
     ) where

import Control.Monad            (unless)
import Control.Monad.State.Lazy (get)
import Control.Monad.Trans      (liftIO)

import Data.List     (unzip3, intercalate, nubBy, sortBy, elemIndex)
import Data.Function (on)

import Data.SBV.Core.Data

import Data.SBV.Core.Symbolic   (QueryState(..), Query(..), SMTModel(..), SMTResult(..), State(..))

import Data.SBV.Utils.SExpr

import Data.SBV.Control.Types
import Data.SBV.Control.Utils

import Data.IORef (readIORef)

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
        go (ENum (i, _)) = show i
        go (EReal   r)   = show r
        go (EFloat  f)   = show f
        go (EDouble d)   = show d
        go (EApp [x])    = go x
        go (EApp ss)     = "(" ++ unwords (map go ss) ++ ")"

-- | Ask solver for info.
getInfo :: SMTInfoFlag -> Query SMTInfoResponse
getInfo flag = do
    let cmd = "(get-info " ++ show flag ++ ")"
        bad = unexpected "getInfo" cmd "a valid get-info response" Nothing

        isAllStatistics AllStatistics = True
        isAllStatistics _             = False

        isAllStat = isAllStatistics flag

        render = serialize True

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
                 EApp [ECon ":reason-unknown", ECon "memout"]              -> return $ Resp_ReasonUnknown UnknownMemOut
                 EApp [ECon ":reason-unknown", ECon "incomplete"]          -> return $ Resp_ReasonUnknown UnknownIncomplete
                 EApp (ECon ":reason-unknown" : o)                         -> return $ Resp_ReasonUnknown (UnknownOther (render (EApp o)))
                 EApp (ECon ":version" : o)                                -> return $ Resp_Version (render (EApp o))
                 EApp (ECon s : o)                                         -> return $ Resp_InfoKeyword s (map render o)
                 _                                                         -> bad r Nothing

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

-- | Issue check-sat and get an SMT Result out.
getSMTResult :: Query SMTResult
getSMTResult = do cfg <- getConfig
                  cs  <- checkSat
                  case cs of
                    Unsat -> return $ Unsatisfiable cfg
                    Sat   -> Satisfiable cfg <$> getModel
                    Unk   -> Unknown     cfg <$> getModel

-- | Issue check-sat and get an SMT result together with objectives to form a result out.
getSMTResultWithObjectives :: Query SMTResult
getSMTResultWithObjectives = do cfg <- getConfig
                                cs  <- checkSat
                                case cs of
                                  Unsat -> return $ Unsatisfiable cfg
                                  Sat   -> classifyModel cfg <$> getModelWithObjectives
                                  Unk   -> Unknown       cfg <$> getModelWithObjectives
   where classifyModel :: SMTConfig -> SMTModel -> SMTResult
         classifyModel cfg m = case filter (not . isRegularCW . snd) (modelObjectives m) of
                                 [] -> Satisfiable cfg m
                                 _  -> SatExtField cfg m

-- | Collect model values. It is implicitly assumed that we are in a check-sat
-- context. See 'getSMTResult' for a variant that issues a check-sat first and
-- returns an 'SMTResult'.
getModel :: Query SMTModel
getModel = do State{runMode, rinps} <- get
              cfg  <- getConfig
              inps <- liftIO $ reverse <$> readIORef rinps
              let vars :: [NamedSymVar]
                  vars = case runMode of
                           m@CodeGen         -> error $ "SBV.getModel: Model is not available in mode: " ++ show m
                           m@Concrete        -> error $ "SBV.getModel: Model is not available in mode: " ++ show m
                           SMTMode _ isSAT _ -> -- for "sat", display the prefix existentials. for "proof", display the prefix universals
                                                let allModelInputs = if isSAT then takeWhile ((/= ALL) . fst) inps
                                                                              else takeWhile ((== ALL) . fst) inps

                                                    sortByNodeId :: [NamedSymVar] -> [NamedSymVar]
                                                    sortByNodeId = sortBy (compare `on` (\(SW _ n, _) -> n))

                                                in sortByNodeId [nv | (_, nv@(_, n)) <- allModelInputs, not (isNonModelVar cfg n)]

              assocs <- mapM (\(sw, n) -> (n, ) <$> getValueCW sw) vars

              return SMTModel { modelObjectives = []
                              , modelAssocs     = assocs
                              }

-- | Collect model values, together with objectives.
-- NB. This is very much likely Z3 specific, and will need to be reworked
-- if objectives find their way into proper SMTLib treatment.
getModelWithObjectives :: Query SMTModel
getModelWithObjectives = do -- When we start, check-sat is already issued, and we are looking at objective values
                            r <- retrieveResponse Nothing

                            State{rinps} <- get
                            inpSWs <- liftIO $ (reverse . map (fst . snd)) <$> readIORef rinps

                            let bad = unexpected "getModelWithObjectives" "check-sat" "a list of objective values" Nothing

                                objectiveValues = parse r bad $ \case EApp (ECon "objectives" : es) -> map (getObjValue (bad r Nothing) inpSWs) es
                                                                      _                             -> bad r Nothing

                            -- Now do a regular getModel call, and return together with the objectives
                            m <- getModel
                            return m {modelObjectives = objectiveValues}

-- | Parse an objective value out.
getObjValue :: (forall a. Maybe [String] -> a) -> [SW] -> SExpr -> (String, GeneralizedCW)
getObjValue bailOut inpSWs (EApp [ECon nm, v]) = (nm, extract v)
  where s :: SW
        s = case [sw | sw <- inpSWs, show sw == nm] of
              [sw] -> sw
              _    -> bailOut $ Just [ "Unknown objective value for " ++ nm
                                     , "Was expecting one of: " ++ intercalate ", "  (map show inpSWs)
                                     ]

        k = kindOf s

        isIntegral sw = isBoolean sw || isBounded sw || isInteger sw

        getUIIndex (KUserSort  _ (Right xs)) i = i `elemIndex` xs
        getUIIndex _                         _ = Nothing

        extract (ENum    i) | isIntegral      s = RegularCW  $ mkConstCW  k (fst i)
        extract (EReal   i) | isReal          s = RegularCW  $ CW KReal   (CWAlgReal i)
        extract (EFloat  i) | isFloat         s = RegularCW  $ CW KFloat  (CWFloat   i)
        extract (EDouble i) | isDouble        s = RegularCW  $ CW KDouble (CWDouble  i)
        extract (ECon    i) | isUninterpreted s = RegularCW  $ CW k       (CWUserSort (getUIIndex k i, i))

        -- Exhausted regular values, look for infinities and such:
        extract val                             = ExtendedCW $ cvt (simplify val)

        -- Convert to an extended expression. Hopefully complete!
        cvt :: SExpr -> ExtCW
        cvt (ECon "oo")                    = Infinite  k
        cvt (ECon "epsilon")               = Epsilon   k
        cvt (EApp [ECon "interval", x, y]) = Interval  (cvt x) (cvt y)
        cvt (ENum    (i, _))               = BoundedCW $ mkConstCW k i
        cvt (EReal   r)                    = BoundedCW $ CW k $ CWAlgReal r
        cvt (EFloat  f)                    = BoundedCW $ CW k $ CWFloat   f
        cvt (EDouble d)                    = BoundedCW $ CW k $ CWDouble  d
        cvt (EApp [ECon "+", x, y])        = AddExtCW (cvt x) (cvt y)
        cvt (EApp [ECon "*", x, y])        = MulExtCW (cvt x) (cvt y)
        -- Nothing else should show up, hopefully!
        cvt e = bailOut $ Just [ "Unable to understand solver output."
                               , "While trying to process: " ++ show e
                               ]

        -- drop the pesky to_real's that Z3 produces.. Cool but useless.
        simplify :: SExpr -> SExpr
        simplify (EApp [ECon "to_real", n]) = n
        simplify (EApp xs)                  = EApp (map simplify xs)
        simplify e                          = e
getObjValue bailOut _ _ = bailOut Nothing


-- | Check for satisfiability, under the given conditions. Similar to 'checkSat'
-- except it allows making further assumptions as captured by the first argument
-- of booleans. If the result is 'Unsat', the user will also receive a subset of
-- the given assumptions that led to the 'Unsat' conclusion. Note that while this
-- set will be a subset of the inputs, it is not necessarily guaranteed to be minimal.
--
-- You must have arranged for the production of unsat assumptions
-- first (/via/ @'setOption' 'ProduceUnsatAssumptions' 'True'@)
-- for this call to not error out!
--
-- Usage note: 'getUnsatCore' is usually easier to use than 'checkSatAssuming', as it
-- allows the use of named assertions, as obtained by 'namedAssert'. If 'getUnsatCore'
-- fills your needs, you should definitely prefer it over 'checkSatAssuming'.
checkSatAssuming :: [SBool] -> Query (CheckSatResult, Maybe [SBool])
checkSatAssuming sBools = do
        -- sigh.. SMT-Lib requires the values to be literals only. So, create proxies.
        let mkAssumption st = do swsOriginal <- mapM (\sb -> sbvToSW st sb >>= \sw -> return (sw, sb)) sBools

                                 -- drop duplicates and trues
                                 let swbs = [p | p@(sw, _) <- nubBy ((==) `on` fst) swsOriginal, sw /= trueSW]

                                     translate (sw, sb) = (nm, decls, (proxy, sb))
                                        where nm    = show sw
                                              proxy = "__assumption_proxy_" ++ nm
                                              decls = [ "(declare-const " ++ proxy ++ " Bool)"
                                                      , "(assert (= " ++ proxy ++ " " ++ nm ++ "))"
                                                      ]

                                 return $ map translate swbs

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

        let grabUnsat = do as <- getUnsatAssumptions origNames proxyMap
                           return (Unsat, Just as)

        parse r bad $ \case ECon "sat"     -> return (Sat, Nothing)
                            ECon "unsat"   -> grabUnsat
                            ECon "unknown" -> return (Unk, Nothing)
                            _              -> bad r Nothing

-- | The current assertion stack depth, i.e., #push - #pops after start. Always non-negative.
getAssertionStackDepth :: Query Int
getAssertionStackDepth = queryAssertionStackDepth <$> getQueryState

-- | Push the context, entering a new one. Pushes multiple levels if /n/ > 1.
push :: Int -> Query ()
push i
 | i <= 0 = error $ "Data.SBV: push requires a strictly positive level argument, received: " ++ show i
 | True   = do depth <- getAssertionStackDepth
               send True $ "(push " ++ show i ++ ")"
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
                                     modifyQueryState $ \s -> s{queryAssertionStackDepth = depth - i}
   where shl 1 = "one level"
         shl n = show n ++ " levels"

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
-- unsat cores to be produced first (/via/ @'setOption' 'ProduceUnsatCores' 'True'@)
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

-- | Retrieve the proof. Note you must have arranged for
-- proofs to be produced first (/via/ @'setOption' 'ProduceProofs' 'True'@)
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
                                  , "to make sure the solver is ready for producing proofs."
                                  , "and that there is a proof by first issuing a 'checkSat' call."
                                  ]


        r <- ask cmd

        -- we only care about the fact that we can parse the output, so the
        -- result of parsing is ignored.
        parse r bad $ \_ -> return r

-- | Retrieve assertions. Note you must have arranged for
-- assertions to be available first (/via/ @'setOption' 'ProduceAssertions' 'True'@)
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

-- | Make an assignment. The type 'Assignment' is abstract, see 'success' for an example use case.
infix 1 |->
(|->) :: SymWord a => SBV a -> a -> Assignment
SBV a |-> v = case literal v of
                SBV (SVal _ (Left cw)) -> Assign a cw
                r                      -> error $ "Data.SBV: Impossible happened in |->: Cannot construct a CW with literal: " ++ show r

-- | Produce the query result from an assignment.
mkResult :: [Assignment] -> Query SMTResult
mkResult asgns = do QueryState{queryConfig} <- getQueryState

                    let grabValues st = do let extract (Assign s n) = sbvToSW st (SBV s) >>= \sw -> return (sw, n)

                                           modelAssignment <- mapM extract asgns

                                           inps <- reverse <$> readIORef (rinps st)

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
                                                                   ]
                                                                ++ [ align misTag ++ intercalate ", "  missing | not (null missing)]
                                                                ++ [ align extTag ++ intercalate ", "  extra   | not (null extra)  ]
                                                                ++ [ align dupTag ++ intercalate ", "  dup     | not (null dup)    ]
                                                                ++ [ "*** Data.SBV: Check your query result construction!" ]

                                           return modelAssignment

                    assocs <- inNewContext grabValues

                    let m = SMTModel { modelObjectives = []
                                     , modelAssocs     = [(show s, c) | (s, c) <- assocs]
                                     }

                    return $ Satisfiable queryConfig m
