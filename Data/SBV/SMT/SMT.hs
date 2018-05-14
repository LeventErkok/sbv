-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Abstraction of SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE NamedFieldPuns             #-}

module Data.SBV.SMT.SMT (
       -- * Model extraction
         Modelable(..)
       , SatModel(..), genParse
       , extractModels, getModelValues
       , getModelDictionaries, getModelUninterpretedValues
       , displayModels, showModel

       -- * Standard prover engine
       , standardEngine

       -- * Results of various tasks
       , ThmResult(..)
       , SatResult(..)
       , AllSatResult(..)
       , SafeResult(..)
       , OptimizeResult(..)
       )
       where

import qualified Control.Exception as C

import Control.Concurrent (newEmptyMVar, takeMVar, putMVar, forkIO)
import Control.DeepSeq    (NFData(..))
import Control.Monad      (zipWithM)
import Data.Char          (isSpace)
import Data.Maybe         (fromMaybe)
import Data.Int           (Int8, Int16, Int32, Int64)
import Data.List          (intercalate, isPrefixOf)
import Data.Word          (Word8, Word16, Word32, Word64)

import Data.IORef (readIORef, writeIORef)

import Data.Time          (getZonedTime, defaultTimeLocale, formatTime, diffUTCTime, getCurrentTime)

import System.Directory   (findExecutable)
import System.Environment (getEnv)
import System.Exit        (ExitCode(..))
import System.IO          (hClose, hFlush, hPutStrLn, hGetContents, hGetLine)
import System.Process     (runInteractiveProcess, waitForProcess, terminateProcess)

import qualified Data.Map as M

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (SMTEngine, State(..))

import Data.SBV.SMT.Utils     (showTimeoutValue, alignPlain, alignDiagnostic, debug, mergeSExpr, SMTException(..))

import Data.SBV.Utils.PrettyNum
import Data.SBV.Utils.Lib       (joinArgs, splitArgs)
import Data.SBV.Utils.SExpr     (parenDeficit)
import Data.SBV.Utils.TDiff     (Timing(..), showTDiff)

import qualified System.Timeout as Timeout (timeout)

-- | Extract the final configuration from a result
resultConfig :: SMTResult -> SMTConfig
resultConfig (Unsatisfiable c _) = c
resultConfig (Satisfiable   c _) = c
resultConfig (SatExtField   c _) = c
resultConfig (Unknown       c _) = c
resultConfig (ProofError    c _) = c

-- | A 'prove' call results in a 'ThmResult'
newtype ThmResult = ThmResult SMTResult
                  deriving NFData

-- | A 'sat' call results in a 'SatResult'
-- The reason for having a separate 'SatResult' is to have a more meaningful 'Show' instance.
newtype SatResult = SatResult SMTResult
                  deriving NFData

-- | An 'allSat' call results in a 'AllSatResult'. The first boolean says whether we
-- hit the max-model limit as we searched. The second boolean says whether
-- there were prefix-existentials.
newtype AllSatResult = AllSatResult (Bool, Bool, [SMTResult])

-- | A 'safe' call results in a 'SafeResult'
newtype SafeResult   = SafeResult   (Maybe String, String, SMTResult)

-- | An 'optimize' call results in a 'OptimizeResult'. In the 'ParetoResult' case, the boolean is 'True'
-- if we reached pareto-query limit and so there might be more unqueried results remaining. If 'False',
-- it means that we have all the pareto fronts returned. See the 'Pareto' 'OptimizeStyle' for details.
data OptimizeResult = LexicographicResult SMTResult
                    | ParetoResult        (Bool, [SMTResult])
                    | IndependentResult   [(String, SMTResult)]

-- User friendly way of printing theorem results
instance Show ThmResult where
  show (ThmResult r) = showSMTResult "Q.E.D."
                                     "Unknown"
                                     "Falsifiable" "Falsifiable. Counter-example:\n" "Falsifiable in an extension field:\n" r

-- User friendly way of printing satisfiablity results
instance Show SatResult where
  show (SatResult r) = showSMTResult "Unsatisfiable"
                                     "Unknown"
                                     "Satisfiable" "Satisfiable. Model:\n" "Satisfiable in an extension field. Model:\n" r

-- User friendly way of printing safety results
instance Show SafeResult where
   show (SafeResult (mbLoc, msg, r)) = showSMTResult (tag "No violations detected")
                                                     (tag "Unknown")
                                                     (tag "Violated") (tag "Violated. Model:\n") (tag "Violated in an extension field:\n") r
        where loc   = maybe "" (++ ": ") mbLoc
              tag s = loc ++ msg ++ ": " ++ s

-- The Show instance of AllSatResults. Note that we have to be careful in being lazy enough
-- as the typical use case is to pull results out as they become available.
instance Show AllSatResult where
  show (AllSatResult (l, e, xs)) = go (0::Int) xs
    where uniqueWarn | e    = " (Unique up to prefix existentials.)"
                     | True = ""
          go c (s:ss) = let c'      = c+1
                            (ok, o) = sh c' s
                        in c' `seq` if ok then o ++ "\n" ++ go c' ss else o
          go c []     = case (l, c) of
                          (True,  _) -> "Search stopped since model count request was reached." ++ uniqueWarn
                          (False, 0) -> "No solutions found."
                          (False, 1) -> "This is the only solution." ++ uniqueWarn
                          (False, _) -> "Found " ++ show c ++ " different solutions." ++ uniqueWarn
          sh i c = (ok, showSMTResult "Unsatisfiable"
                                      "Unknown"
                                      ("Solution #" ++ show i ++ ":\nSatisfiable") ("Solution #" ++ show i ++ ":\n")
                                      ("Solution $" ++ show i ++ " in an extension field:\n")
                                      c)
              where ok = case c of
                           Satisfiable{} -> True
                           _             -> False

-- Show instance for optimization results
instance Show OptimizeResult where
  show res = case res of
               LexicographicResult r   -> sh id r

               IndependentResult   rs  -> multi "objectives" (map (uncurry shI) rs)

               ParetoResult (False, [r]) -> sh (\s -> "Unique pareto front: " ++ s) r
               ParetoResult (False, rs)  -> multi "pareto optimal values" (zipWith shP [(1::Int)..] rs)
               ParetoResult (True,  rs)  ->    multi "pareto optimal values" (zipWith shP [(1::Int)..] rs)
                                           ++ "\n*** Note: Pareto-front extraction was terminated before stream was ended as requested by the user."
                                           ++ "\n***       There might be other (potentially infinitely more) results."

       where multi w [] = "There are no " ++ w ++ " to display models for."
             multi _ xs = intercalate "\n" xs

             shI n = sh (\s -> "Objective "     ++ show n ++ ": " ++ s)
             shP i = sh (\s -> "Pareto front #" ++ show i ++ ": " ++ s)

             sh tag = showSMTResult (tag "Unsatisfiable.")
                                    (tag "Unknown.")
                                    (tag "Optimal with no assignments.")
                                    (tag "Optimal model:" ++ "\n")
                                    (tag "Optimal in an extension field:" ++ "\n")

-- | Instances of 'SatModel' can be automatically extracted from models returned by the
-- solvers. The idea is that the sbv infrastructure provides a stream of 'CW''s (constant-words)
-- coming from the solver, and the type @a@ is interpreted based on these constants. Many typical
-- instances are already provided, so new instances can be declared with relative ease.
--
-- Minimum complete definition: 'parseCWs'
class SatModel a where
  -- | Given a sequence of constant-words, extract one instance of the type @a@, returning
  -- the remaining elements untouched. If the next element is not what's expected for this
  -- type you should return 'Nothing'
  parseCWs  :: [CW] -> Maybe (a, [CW])
  -- | Given a parsed model instance, transform it using @f@, and return the result.
  -- The default definition for this method should be sufficient in most use cases.
  cvtModel  :: (a -> Maybe b) -> Maybe (a, [CW]) -> Maybe (b, [CW])
  cvtModel f x = x >>= \(a, r) -> f a >>= \b -> return (b, r)

  default parseCWs :: Read a => [CW] -> Maybe (a, [CW])
  parseCWs (CW _ (CWUserSort (_, s)) : r) = Just (read s, r)
  parseCWs _                              = Nothing

-- | Parse a signed/sized value from a sequence of CWs
genParse :: Integral a => Kind -> [CW] -> Maybe (a, [CW])
genParse k (x@(CW _ (CWInteger i)):r) | kindOf x == k = Just (fromIntegral i, r)
genParse _ _                                          = Nothing

-- | Base case for 'SatModel' at unit type. Comes in handy if there are no real variables.
instance SatModel () where
  parseCWs xs = return ((), xs)

-- | 'Bool' as extracted from a model
instance SatModel Bool where
  parseCWs xs = do (x, r) <- genParse KBool xs
                   return ((x :: Integer) /= 0, r)

-- | 'Word8' as extracted from a model
instance SatModel Word8 where
  parseCWs = genParse (KBounded False 8)

-- | 'Int8' as extracted from a model
instance SatModel Int8 where
  parseCWs = genParse (KBounded True 8)

-- | 'Word16' as extracted from a model
instance SatModel Word16 where
  parseCWs = genParse (KBounded False 16)

-- | 'Int16' as extracted from a model
instance SatModel Int16 where
  parseCWs = genParse (KBounded True 16)

-- | 'Word32' as extracted from a model
instance SatModel Word32 where
  parseCWs = genParse (KBounded False 32)

-- | 'Int32' as extracted from a model
instance SatModel Int32 where
  parseCWs = genParse (KBounded True 32)

-- | 'Word64' as extracted from a model
instance SatModel Word64 where
  parseCWs = genParse (KBounded False 64)

-- | 'Int64' as extracted from a model
instance SatModel Int64 where
  parseCWs = genParse (KBounded True 64)

-- | 'Integer' as extracted from a model
instance SatModel Integer where
  parseCWs = genParse KUnbounded

-- | 'AlgReal' as extracted from a model
instance SatModel AlgReal where
  parseCWs (CW KReal (CWAlgReal i) : r) = Just (i, r)
  parseCWs _                            = Nothing

-- | 'Float' as extracted from a model
instance SatModel Float where
  parseCWs (CW KFloat (CWFloat i) : r) = Just (i, r)
  parseCWs _                           = Nothing

-- | 'Double' as extracted from a model
instance SatModel Double where
  parseCWs (CW KDouble (CWDouble i) : r) = Just (i, r)
  parseCWs _                             = Nothing

-- | 'CW' as extracted from a model; trivial definition
instance SatModel CW where
  parseCWs (cw : r) = Just (cw, r)
  parseCWs []       = Nothing

-- | A rounding mode, extracted from a model. (Default definition suffices)
instance SatModel RoundingMode

-- | A list of values as extracted from a model. When reading a list, we
-- go as long as we can (maximal-munch). Note that this never fails, as
-- we can always return the empty list!
instance SatModel a => SatModel [a] where
  parseCWs [] = Just ([], [])
  parseCWs xs = case parseCWs xs of
                  Just (a, ys) -> case parseCWs ys of
                                    Just (as, zs) -> Just (a:as, zs)
                                    Nothing       -> Just ([], ys)
                  Nothing     -> Just ([], xs)

-- | Tuples extracted from a model
instance (SatModel a, SatModel b) => SatModel (a, b) where
  parseCWs as = do (a, bs) <- parseCWs as
                   (b, cs) <- parseCWs bs
                   return ((a, b), cs)

-- | 3-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c) => SatModel (a, b, c) where
  parseCWs as = do (a,      bs) <- parseCWs as
                   ((b, c), ds) <- parseCWs bs
                   return ((a, b, c), ds)

-- | 4-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d) => SatModel (a, b, c, d) where
  parseCWs as = do (a,         bs) <- parseCWs as
                   ((b, c, d), es) <- parseCWs bs
                   return ((a, b, c, d), es)

-- | 5-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e) => SatModel (a, b, c, d, e) where
  parseCWs as = do (a, bs)            <- parseCWs as
                   ((b, c, d, e), fs) <- parseCWs bs
                   return ((a, b, c, d, e), fs)

-- | 6-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f) => SatModel (a, b, c, d, e, f) where
  parseCWs as = do (a, bs)               <- parseCWs as
                   ((b, c, d, e, f), gs) <- parseCWs bs
                   return ((a, b, c, d, e, f), gs)

-- | 7-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f, SatModel g) => SatModel (a, b, c, d, e, f, g) where
  parseCWs as = do (a, bs)                  <- parseCWs as
                   ((b, c, d, e, f, g), hs) <- parseCWs bs
                   return ((a, b, c, d, e, f, g), hs)

-- | Various SMT results that we can extract models out of.
class Modelable a where
  -- | Is there a model?
  modelExists :: a -> Bool

  -- | Extract assignments of a model, the result is a tuple where the first argument (if True)
  -- indicates whether the model was "probable". (i.e., if the solver returned unknown.)
  getModelAssignment :: SatModel b => a -> Either String (Bool, b)

  -- | Extract a model dictionary. Extract a dictionary mapping the variables to
  -- their respective values as returned by the SMT solver. Also see `getModelDictionaries`.
  getModelDictionary :: a -> M.Map String CW

  -- | Extract a model value for a given element. Also see `getModelValues`.
  getModelValue :: SymWord b => String -> a -> Maybe b
  getModelValue v r = fromCW `fmap` (v `M.lookup` getModelDictionary r)

  -- | Extract a representative name for the model value of an uninterpreted kind.
  -- This is supposed to correspond to the value as computed internally by the
  -- SMT solver; and is unportable from solver to solver. Also see `getModelUninterpretedValues`.
  getModelUninterpretedValue :: String -> a -> Maybe String
  getModelUninterpretedValue v r = case v `M.lookup` getModelDictionary r of
                                     Just (CW _ (CWUserSort (_, s))) -> Just s
                                     _                               -> Nothing

  -- | A simpler variant of 'getModelAssignment' to get a model out without the fuss.
  extractModel :: SatModel b => a -> Maybe b
  extractModel a = case getModelAssignment a of
                     Right (_, b) -> Just b
                     _            -> Nothing

  -- | Extract model objective values, for all optimization goals.
  getModelObjectives :: a -> M.Map String GeneralizedCW

  -- | Extract the value of an objective
  getModelObjectiveValue :: String -> a -> Maybe GeneralizedCW
  getModelObjectiveValue v r = v `M.lookup` getModelObjectives r

-- | Return all the models from an 'allSat' call, similar to 'extractModel' but
-- is suitable for the case of multiple results.
extractModels :: SatModel a => AllSatResult -> [a]
extractModels (AllSatResult (_, _, xs)) = [ms | Right (_, ms) <- map getModelAssignment xs]

-- | Get dictionaries from an all-sat call. Similar to `getModelDictionary`.
getModelDictionaries :: AllSatResult -> [M.Map String CW]
getModelDictionaries (AllSatResult (_, _, xs)) = map getModelDictionary xs

-- | Extract value of a variable from an all-sat call. Similar to `getModelValue`.
getModelValues :: SymWord b => String -> AllSatResult -> [Maybe b]
getModelValues s (AllSatResult (_, _, xs)) =  map (s `getModelValue`) xs

-- | Extract value of an uninterpreted variable from an all-sat call. Similar to `getModelUninterpretedValue`.
getModelUninterpretedValues :: String -> AllSatResult -> [Maybe String]
getModelUninterpretedValues s (AllSatResult (_, _, xs)) =  map (s `getModelUninterpretedValue`) xs

-- | 'ThmResult' as a generic model provider
instance Modelable ThmResult where
  getModelAssignment (ThmResult r) = getModelAssignment r
  modelExists        (ThmResult r) = modelExists r
  getModelDictionary (ThmResult r) = getModelDictionary r
  getModelObjectives (ThmResult r) = getModelObjectives r

-- | 'SatResult' as a generic model provider
instance Modelable SatResult where
  getModelAssignment (SatResult r) = getModelAssignment r
  modelExists        (SatResult r) = modelExists r
  getModelDictionary (SatResult r) = getModelDictionary r
  getModelObjectives (SatResult r) = getModelObjectives r

-- | 'SMTResult' as a generic model provider
instance Modelable SMTResult where
  getModelAssignment (Unsatisfiable _ _) = Left "SBV.getModelAssignment: Unsatisfiable result"
  getModelAssignment (Satisfiable _ m)   = Right (False, parseModelOut m)
  getModelAssignment (SatExtField _ _)   = Left "SBV.getModelAssignment: The model is in an extension field"
  getModelAssignment (Unknown _ m)       = Left $ "SBV.getModelAssignment: Solver state is unknown: " ++ m
  getModelAssignment (ProofError _ s)    = error $ unlines $ "Backend solver complains: " : s

  modelExists Satisfiable{}   = True
  modelExists Unknown{}       = False -- don't risk it
  modelExists _               = False

  getModelDictionary Unsatisfiable{}   = M.empty
  getModelDictionary (Satisfiable _ m) = M.fromList (modelAssocs m)
  getModelDictionary SatExtField{}     = M.empty
  getModelDictionary Unknown{}         = M.empty
  getModelDictionary ProofError{}      = M.empty

  getModelObjectives Unsatisfiable{}   = M.empty
  getModelObjectives (Satisfiable _ m) = M.fromList (modelObjectives m)
  getModelObjectives (SatExtField _ m) = M.fromList (modelObjectives m)
  getModelObjectives Unknown{}         = M.empty
  getModelObjectives ProofError{}      = M.empty

-- | Extract a model out, will throw error if parsing is unsuccessful
parseModelOut :: SatModel a => SMTModel -> a
parseModelOut m = case parseCWs [c | (_, c) <- modelAssocs m] of
                   Just (x, []) -> x
                   Just (_, ys) -> error $ "SBV.parseModelOut: Partially constructed model; remaining elements: " ++ show ys
                   Nothing      -> error $ "SBV.parseModelOut: Cannot construct a model from: " ++ show m

-- | Given an 'allSat' call, we typically want to iterate over it and print the results in sequence. The
-- 'displayModels' function automates this task by calling 'disp' on each result, consecutively. The first
-- 'Int' argument to 'disp' 'is the current model number. The second argument is a tuple, where the first
-- element indicates whether the model is alleged (i.e., if the solver is not sure, returing Unknown)
displayModels :: SatModel a => (Int -> (Bool, a) -> IO ()) -> AllSatResult -> IO Int
displayModels disp (AllSatResult (_, _, ms)) = do
    inds <- zipWithM display [a | Right a <- map (getModelAssignment . SatResult) ms] [(1::Int)..]
    return $ last (0:inds)
  where display r i = disp i r >> return i

-- | Show an SMTResult; generic version
showSMTResult :: String -> String -> String -> String -> String -> SMTResult -> String
showSMTResult unsatMsg unkMsg satMsg satMsgModel satExtMsg result = case result of
  Unsatisfiable _ uc            -> unsatMsg ++ showUnsatCore uc
  Satisfiable _ (SMTModel _ []) -> satMsg
  Satisfiable _ m               -> satMsgModel ++ showModel cfg m
  SatExtField _ (SMTModel b _)  -> satExtMsg   ++ showModelDictionary cfg b
  Unknown     _ r               -> unkMsg ++ ".\n" ++ "  Reason: " `alignPlain` r
  ProofError  _ []              -> "*** An error occurred. No additional information available. Try running in verbose mode"
  ProofError  _ ls              -> "*** An error occurred.\n" ++ intercalate "\n" (map ("***  " ++) ls)
 where cfg = resultConfig result
       showUnsatCore Nothing   = ""
       showUnsatCore (Just xs) = ". Unsat core:\n" ++ intercalate "\n" ["    " ++ x | x <- xs]

-- | Show a model in human readable form. Ignore bindings to those variables that start
-- with "__internal_sbv_" and also those marked as "nonModelVar" in the config; as these are only for internal purposes
showModel :: SMTConfig -> SMTModel -> String
showModel cfg model = showModelDictionary cfg [(n, RegularCW c) | (n, c) <- modelAssocs model]

-- | Show bindings in a generalized model dictionary, tabulated
showModelDictionary :: SMTConfig -> [(String, GeneralizedCW)] -> String
showModelDictionary cfg allVars
   | null allVars
   = "[There are no variables bound by the model.]"
   | null relevantVars
   = "[There are no model-variables bound by the model.]"
   | True
   = intercalate "\n" . display . map shM $ relevantVars
  where relevantVars  = filter (not . ignore) allVars
        ignore (s, _) = "__internal_sbv_" `isPrefixOf` s || isNonModelVar cfg s

        shM (s, RegularCW v) = let vs = shCW cfg v in ((length s, s), (vlength vs, vs))
        shM (s, other)       = let vs = show other in ((length s, s), (vlength vs, vs))

        display svs   = map line svs
           where line ((_, s), (_, v)) = "  " ++ right (nameWidth - length s) s ++ " = " ++ left (valWidth - lTrimRight (valPart v)) v
                 nameWidth             = maximum $ 0 : [l | ((l, _), _) <- svs]
                 valWidth              = maximum $ 0 : [l | (_, (l, _)) <- svs]

        right p s = s ++ replicate p ' '
        left  p s = replicate p ' ' ++ s
        vlength s = case dropWhile (/= ':') (reverse (takeWhile (/= '\n') s)) of
                      (':':':':r) -> length (dropWhile isSpace r)
                      _           -> length s -- conservative

        valPart ""          = ""
        valPart (':':':':_) = ""
        valPart (x:xs)      = x : valPart xs

        lTrimRight = length . dropWhile isSpace . reverse

-- | Show a constant value, in the user-specified base
shCW :: SMTConfig -> CW -> String
shCW = sh . printBase
  where sh 2  = binS
        sh 10 = show
        sh 16 = hexS
        sh n  = \w -> show w ++ " -- Ignoring unsupported printBase " ++ show n ++ ", use 2, 10, or 16."

-- | Helper function to spin off to an SMT solver.
pipeProcess :: SMTConfig -> State -> String -> [String] -> String -> (State -> IO a) -> IO a
pipeProcess cfg ctx execName opts pgm continuation = do
    mbExecPath <- findExecutable execName
    case mbExecPath of
      Nothing      -> error $ unlines [ "Unable to locate executable for " ++ show (name (solver cfg))
                                      , "Executable specified: " ++ show execName
                                      ]

      Just execPath -> runSolver cfg ctx execPath opts pgm continuation
                       `C.catches`
                        [ C.Handler (\(e :: SMTException)    -> C.throwIO e)
                        , C.Handler (\(e :: C.ErrorCall)     -> C.throwIO e)
                        , C.Handler (\(e :: C.SomeException) -> error $ unlines [ "Failed to start the external solver:\n" ++ show e
                                                                                , "Make sure you can start " ++ show execPath
                                                                                , "from the command line without issues."
                                                                                ])
                        ]

-- | A standard engine interface. Most solvers follow-suit here in how we "chat" to them..
standardEngine :: String
               -> String
               -> SMTEngine
standardEngine envName envOptName cfg ctx pgm continuation = do

    execName <-                    getEnv envName     `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
    execOpts <- (splitArgs `fmap`  getEnv envOptName) `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg) cfg))

    let cfg' = cfg {solver = (solver cfg) {executable = execName, options = const execOpts}}

    standardSolver cfg' ctx pgm continuation

-- | A standard solver interface. If the solver is SMT-Lib compliant, then this function should suffice in
-- communicating with it.
standardSolver :: SMTConfig       -- ^ The currrent configuration
               -> State           -- ^ Context in which we are running
               -> String          -- ^ The program
               -> (State -> IO a) -- ^ The continuation
               -> IO a
standardSolver config ctx pgm continuation = do
    let msg s    = debug config ["** " ++ s]
        smtSolver= solver config
        exec     = executable smtSolver
        opts     = options smtSolver config
    msg $ "Calling: "  ++ (exec ++ (if null opts then "" else " ") ++ joinArgs opts)
    rnf pgm `seq` pipeProcess config ctx exec opts pgm continuation

-- | An internal type to track of solver interactions
data SolverLine = SolverRegular   String  -- ^ All is well
                | SolverTimeout   String  -- ^ Timeout expired
                | SolverException String  -- ^ Something else went wrong

-- | A variant of 'readProcessWithExitCode'; except it deals with SBV continuations
runSolver :: SMTConfig -> State -> FilePath -> [String] -> String -> (State -> IO a) -> IO a
runSolver cfg ctx execPath opts pgm continuation
 = do let nm  = show (name (solver cfg))
          msg = debug cfg . map ("*** " ++)

      (send, ask, getResponseFromSolver, terminateSolver, cleanUp, pid) <- do
                (inh, outh, errh, pid) <- runInteractiveProcess execPath opts Nothing Nothing

                let -- send a command down, but check that we're balanced in parens. If we aren't
                    -- this is most likely an SBV bug.
                    send :: Maybe Int -> String -> IO ()
                    send mbTimeOut command
                      | parenDeficit command /= 0
                      = error $ unlines [ ""
                                        , "*** Data.SBV: Unbalanced input detected."
                                        , "***"
                                        , "***   Sending: " ++ command
                                        , "***"
                                        , "*** This is most likely an SBV bug. Please report!"
                                        ]
                      | True
                      = do hPutStrLn inh command
                           hFlush inh
                           recordTranscript (transcript cfg) $ Left (command, mbTimeOut)

                    -- Send a line, get a whole s-expr. We ignore the pathetic case that there might be a string with an unbalanced parentheses in it in a response.
                    ask :: Maybe Int -> String -> IO String
                    ask mbTimeOut command =
                                  -- solvers don't respond to empty lines or comments; we just pass back
                                  -- success in these cases to keep the illusion of everything has a response
                                  let cmd = dropWhile isSpace command
                                  in if null cmd || ";" `isPrefixOf` cmd
                                     then return "success"
                                     else do send mbTimeOut command
                                             getResponseFromSolver (Just command) mbTimeOut

                    -- Get a response from the solver, with an optional time-out on how long
                    -- to wait. Note that there's *always* a time-out of 5 seconds once we get the
                    -- first line of response, as while the solver might take it's time to respond,
                    -- once it starts responding successive lines should come quickly.
                    getResponseFromSolver :: Maybe String -> Maybe Int -> IO String
                    getResponseFromSolver mbCommand mbTimeOut = do
                                response <- go True 0 []
                                let collated = intercalate "\n" $ reverse response
                                recordTranscript (transcript cfg) $ Right collated
                                return collated

                      where safeGetLine isFirst h =
                                         let timeOutToUse | isFirst = mbTimeOut
                                                          | True    = Just 5000000
                                             timeOutMsg t | isFirst = "User specified timeout of " ++ showTimeoutValue t ++ " exceeded."
                                                          | True    = "A multiline complete response wasn't received before " ++ showTimeoutValue t ++ " exceeded."

                                             -- Like hGetLine, except it keeps getting lines if inside a string.
                                             getFullLine :: IO String
                                             getFullLine = intercalate "\n" . reverse <$> collect False []
                                                where collect inString sofar = do ln <- hGetLine h

                                                                                  let walk inside []           = inside
                                                                                      walk inside ('"':cs)     = walk (not inside) cs
                                                                                      walk inside (_:cs)       = walk inside       cs

                                                                                      stillInside = walk inString ln

                                                                                      sofar' = ln : sofar

                                                                                  if stillInside
                                                                                     then collect True sofar'
                                                                                     else return sofar'

                                         in case timeOutToUse of
                                              Nothing -> SolverRegular <$> getFullLine
                                              Just t  -> do r <- Timeout.timeout t getFullLine
                                                            case r of
                                                              Just l  -> return $ SolverRegular l
                                                              Nothing -> return $ SolverTimeout $ timeOutMsg t


                            go isFirst i sofar = do
                                            errln <- safeGetLine isFirst outh `C.catch` (\(e :: C.SomeException) -> return (SolverException (show e)))
                                            case errln of
                                              SolverRegular ln -> let need  = i + parenDeficit ln
                                                                      -- make sure we get *something*
                                                                      empty = case dropWhile isSpace ln of
                                                                                []      -> True
                                                                                (';':_) -> True   -- yes this does happen! I've seen z3 print out comments on stderr.
                                                                                _       -> False
                                                                  in case (empty, need <= 0) of
                                                                        (True, _)      -> do debug cfg ["[SKIP] " `alignPlain` ln]
                                                                                             go isFirst need sofar
                                                                        (False, False) -> go False   need (ln:sofar)
                                                                        (False, True)  -> return (ln:sofar)

                                              SolverException e -> error $ unlines $ [""
                                                                                     , "*** Error     : " ++ e
                                                                                     , "*** Executable: " ++ execPath
                                                                                     , "*** Options   : " ++ joinArgs opts
                                                                                     ]
                                                                                  ++ [ "*** Request   : " `alignDiagnostic` command                 | Just command <- [mbCommand]]
                                                                                  ++ [ "*** Response  : " `alignDiagnostic` unlines (reverse sofar) | not $ null sofar           ]
                                                                                  ++ [ "***"
                                                                                     , "*** Giving up!"
                                                                                     ]

                                              SolverTimeout e -> do terminateProcess pid -- NB. Do not *wait* for the process, just quit.
                                                                    error $ unlines $ [ ""
                                                                                      , "*** Data.SBV: Timeout."
                                                                                      , "***"
                                                                                      , "***   " ++ e
                                                                                      ]
                                                                                   ++ [ "***   Response so far: " `alignDiagnostic` unlines (reverse sofar) | not $ null sofar]
                                                                                   ++ [ "***   Last command sent was: " `alignDiagnostic` command | Just command <- [mbCommand]]
                                                                                   ++ [ "***   Run with 'verbose=True' for further information" | not (verbose cfg)]
                                                                                   ++ [ "***"
                                                                                      , "*** Giving up!"
                                                                                      ]

                    terminateSolver = do hClose inh
                                         outMVar <- newEmptyMVar
                                         out <- hGetContents outh `C.catch`  (\(e :: C.SomeException) -> return (show e))
                                         _ <- forkIO $ C.evaluate (length out) >> putMVar outMVar ()
                                         err <- hGetContents errh `C.catch`  (\(e :: C.SomeException) -> return (show e))
                                         _ <- forkIO $ C.evaluate (length err) >> putMVar outMVar ()
                                         takeMVar outMVar
                                         takeMVar outMVar
                                         hClose outh `C.catch`  (\(_ :: C.SomeException) -> return ())
                                         hClose errh `C.catch`  (\(_ :: C.SomeException) -> return ())
                                         ex <- waitForProcess pid `C.catch` (\(_ :: C.SomeException) -> return (ExitFailure (-999)))
                                         return (out, err, ex)

                    cleanUp
                      = do (out, err, ex) <- terminateSolver

                           msg $   [ "Solver   : " ++ nm
                                   , "Exit code: " ++ show ex
                                   ]
                                ++ [ "Std-out  : " ++ intercalate "\n           " (lines out) | not (null out)]
                                ++ [ "Std-err  : " ++ intercalate "\n           " (lines err) | not (null err)]

                           case ex of
                             ExitSuccess -> return ()
                             _           -> if ignoreExitCode cfg
                                               then msg ["Ignoring non-zero exit code of " ++ show ex ++ " per user request!"]
                                               else error $ unlines $  [ ""
                                                                       , "*** Failed to complete the call to " ++ nm ++ ":"
                                                                       , "*** Executable   : " ++ execPath
                                                                       , "*** Options      : " ++ joinArgs opts
                                                                       , "*** Exit code    : " ++ show ex
                                                                       ]
                                                                    ++ [ "*** Std-out      : " ++ intercalate "\n                   " (lines out)]
                                                                    ++ [ "*** Std-err      : " ++ intercalate "\n                   " (lines err)]
                                                                    ++ ["Giving up.."]
                return (send, ask, getResponseFromSolver, terminateSolver, cleanUp, pid)

      let executeSolver = do let sendAndGetSuccess :: Maybe Int -> String -> IO ()
                                 sendAndGetSuccess mbTimeOut l
                                   -- The pathetic case when the solver doesn't support queries, so we pretend it responded "success"
                                   -- Currently ABC is the only such solver. Filed a request for ABC at: https://bitbucket.org/alanmi/abc/issues/70/
                                   | not (supportsCustomQueries (capabilities (solver cfg)))
                                   = do send mbTimeOut l
                                        debug cfg ["[ISSUE] " `alignPlain` l]
                                   | True
                                   = do r <- ask mbTimeOut l
                                        case words r of
                                          ["success"] -> debug cfg ["[GOOD] " `alignPlain` l]
                                          _           -> do debug cfg ["[FAIL] " `alignPlain` l]

                                                            let isOption = "(set-option" `isPrefixOf` dropWhile isSpace l

                                                                reason | isOption = [ "Backend solver reports it does not support this option."
                                                                                    , "Check the spelling, and if correct please report this as a"
                                                                                    , "bug/feature request with the solver!"
                                                                                    ]
                                                                       | True     = [ "Check solver response for further information. If your code is correct,"
                                                                                    , "please report this as an issue either with SBV or the solver itself!"
                                                                                    ]

                                                            -- put a sync point here before we die so we consume everything
                                                            mbExtras <- (Right <$> getResponseFromSolver Nothing (Just 5000000)) `C.catch` (\(e :: C.SomeException) -> return (Left (show e)))

                                                            -- Ignore any exceptions from last sync, pointless.
                                                            let extras = case mbExtras of
                                                                           Left _   -> []
                                                                           Right xs -> xs

                                                            (outOrig, errOrig, ex) <- terminateSolver
                                                            let out = intercalate "\n" . lines $ outOrig
                                                                err = intercalate "\n" . lines $ errOrig

                                                                exc = SMTException { smtExceptionDescription = "Data.SBV: Unexpected non-success response from " ++ nm
                                                                                   , smtExceptionSent        = l
                                                                                   , smtExceptionExpected    = "success"
                                                                                   , smtExceptionReceived    = r ++ "\n" ++ extras
                                                                                   , smtExceptionStdOut      = out
                                                                                   , smtExceptionStdErr      = Just err
                                                                                   , smtExceptionExitCode    = Just ex
                                                                                   , smtExceptionConfig      = cfg { solver = (solver cfg) {executable = execPath } }
                                                                                   , smtExceptionReason      = Just reason
                                                                                   , smtExceptionHint        = Nothing
                                                                                   }

                                                            C.throwIO exc

                             -- Mark in the log, mostly.
                             sendAndGetSuccess Nothing "; Automatically generated by SBV. Do not edit."

                             -- First check that the solver supports :print-success
                             let backend = name $ solver cfg
                             if not (supportsCustomQueries (capabilities (solver cfg)))
                                then debug cfg ["** Skipping heart-beat for the solver " ++ show backend]
                                else do let heartbeat = "(set-option :print-success true)"
                                        r <- ask (Just 5000000) heartbeat  -- Give the solver 5s to respond, this should be plenty enough!
                                        case words r of
                                          ["success"]     -> debug cfg ["[GOOD] " ++ heartbeat]
                                          ["unsupported"] -> error $ unlines [ ""
                                                                             , "*** Backend solver (" ++  show backend ++ ") does not support the command:"
                                                                             , "***"
                                                                             , "***     (set-option :print-success true)"
                                                                             , "***"
                                                                             , "*** SBV relies on this feature to coordinate communication!"
                                                                             , "*** Please request this as a feature!"
                                                                             ]
                                          _               -> error $ unlines [ ""
                                                                             , "*** Data.SBV: Failed to initiate contact with the solver!"
                                                                             , "***"
                                                                             , "***   Sent    : " ++ heartbeat
                                                                             , "***   Expected: success"
                                                                             , "***   Received: " ++ r
                                                                             , "***"
                                                                             , "*** Try running in debug mode for further information."
                                                                             ]

                             -- For push/pop support, we require :global-declarations to be true. But not all solvers
                             -- support this. Issue it if supported. (If not, we'll reject pop calls.)
                             if not (supportsGlobalDecls (capabilities (solver cfg)))
                                then debug cfg [ "** Backend solver " ++ show backend ++ " does not support global decls."
                                               , "** Some incremental calls, such as pop, will be limited."
                                               ]
                                else sendAndGetSuccess Nothing "(set-option :global-declarations true)"

                             -- Now dump the program!
                             mapM_ (sendAndGetSuccess Nothing) (mergeSExpr (lines pgm))

                             -- Prepare the query context and ship it off
                             let qs = QueryState { queryAsk                 = ask
                                                 , querySend                = send
                                                 , queryRetrieveResponse    = getResponseFromSolver Nothing
                                                 , queryConfig              = cfg
                                                 , queryTerminate           = cleanUp
                                                 , queryTimeOutValue        = Nothing
                                                 , queryAssertionStackDepth = 0
                                                 , queryTblArrPreserveIndex = Nothing
                                                 }
                                 qsp = queryState ctx

                             mbQS <- readIORef qsp

                             case mbQS of
                               Nothing -> writeIORef qsp (Just qs)
                               Just _  -> error $ unlines [ ""
                                                          , "Data.SBV: Impossible happened, query-state was already set."
                                                          , "Please report this as a bug!"
                                                          ]

                             -- off we go!
                             continuation ctx

      -- NB. Don't use 'bracket' here, as it wouldn't have access to the exception.
      let launchSolver = do startTranscript    (transcript cfg) cfg
                            r <- executeSolver
                            finalizeTranscript (transcript cfg) Nothing
                            recordEndTime      cfg ctx
                            return r

      launchSolver `C.catch` (\(e :: C.SomeException) -> do terminateProcess pid
                                                            ec <- waitForProcess pid
                                                            recordException    (transcript cfg) (show e)
                                                            finalizeTranscript (transcript cfg) (Just ec)
                                                            recordEndTime      cfg ctx
                                                            C.throwIO e)

-- | Compute and report the end time
recordEndTime :: SMTConfig -> State -> IO ()
recordEndTime SMTConfig{timing} state = case timing of
                                           NoTiming        -> return ()
                                           PrintTiming     -> do e <- elapsed
                                                                 putStrLn $ "*** SBV: Elapsed time: " ++ showTDiff e
                                           SaveTiming here -> writeIORef here =<< elapsed
  where elapsed = getCurrentTime >>= \end -> return $ diffUTCTime end (startTime state)

-- | Start a transcript file, if requested.
startTranscript :: Maybe FilePath -> SMTConfig -> IO ()
startTranscript Nothing  _   = return ()
startTranscript (Just f) cfg = do ts <- show <$> getZonedTime
                                  mbExecPath <- findExecutable (executable (solver cfg))
                                  writeFile f $ start ts mbExecPath
  where SMTSolver{name, options} = solver cfg
        start ts mbPath = unlines [ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                                  , ";;; SBV: Starting at " ++ ts
                                  , ";;;"
                                  , ";;;           Solver    : " ++ show name
                                  , ";;;           Executable: " ++ fromMaybe "Unable to locate the executable" mbPath
                                  , ";;;           Options   : " ++ unwords (options cfg)
                                  , ";;;"
                                  , ";;; This file is an auto-generated loadable SMT-Lib file."
                                  , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                                  , ""
                                  ]

-- | Finish up the transcript file.
finalizeTranscript :: Maybe FilePath -> Maybe ExitCode -> IO ()
finalizeTranscript Nothing  _    = return ()
finalizeTranscript (Just f) mbEC = do ts <- show <$> getZonedTime
                                      appendFile f $ end ts
  where end ts = unlines $ [ ""
                           , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                           , ";;;"
                           , ";;; SBV: Finished at " ++ ts
                           ]
                       ++  [ ";;;\n;;; Exit code: " ++ show ec | Just ec <- [mbEC] ]
                       ++  [ ";;;"
                           , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                           ]

-- If requested, record in the transcript file
recordTranscript :: Maybe FilePath -> Either (String, Maybe Int) String -> IO ()
recordTranscript Nothing  _ = return ()
recordTranscript (Just f) m = do tsPre <- formatTime defaultTimeLocale "; [%T%Q" <$> getZonedTime
                                 let ts = take 15 $ tsPre ++ repeat '0'
                                 case m of
                                   Left  (sent, mbTimeOut) -> appendFile f $ unlines $ (ts ++ "] " ++ to mbTimeOut ++ "Sending:") : lines sent
                                   Right recv              -> appendFile f $ unlines $ case lines (dropWhile isSpace recv) of
                                                                                        []  -> [ts ++ "] Received: <NO RESPONSE>"]  -- can't really happen.
                                                                                        [x] -> [ts ++ "] Received: " ++ x]
                                                                                        xs  -> (ts ++ "] Received: ") : map (";   " ++) xs
        where to Nothing  = ""
              to (Just i) = "[Timeout: " ++ showTimeoutValue i ++ "] "
{-# INLINE recordTranscript #-}

-- Record the exception
recordException :: Maybe FilePath -> String -> IO ()
recordException Nothing  _ = return ()
recordException (Just f) m = do ts <- show <$> getZonedTime
                                appendFile f $ exc ts
  where exc ts = unlines $ [ ""
                           , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                           , ";;;"
                           , ";;; SBV: Caught an exception at " ++ ts
                           , ";;;"
                           ]
                        ++ [ ";;;   " ++ l | l <- dropWhile null (lines m) ]
                        ++ [ ";;;"
                           , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                           ]
