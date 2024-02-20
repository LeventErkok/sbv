-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.SMT.SMT
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Abstraction of SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE ViewPatterns               #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SMT.SMT (
       -- * Model extraction
         Modelable(..)
       , SatModel(..), genParse
       , extractModels, getModelValues
       , getModelDictionaries, getModelUninterpretedValues
       , displayModels, showModel, shCV, showModelDictionary

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
import Control.Monad      (zipWithM, mplus)
import Data.Char          (isSpace)
import Data.Maybe         (fromMaybe, isJust)
import Data.Int           (Int8, Int16, Int32, Int64)
import Data.List          (intercalate, isPrefixOf, transpose, isInfixOf)
import Data.Word          (Word8, Word16, Word32, Word64)

import GHC.TypeLits
import Data.Proxy

import Data.IORef (readIORef, writeIORef)

import Data.Time          (getZonedTime, defaultTimeLocale, formatTime, diffUTCTime, getCurrentTime)

import Data.Either(rights)

import System.Directory   (findExecutable)
import System.Environment (getEnv)
import System.Exit        (ExitCode(..))
import System.IO          (hClose, hFlush, hPutStrLn, hGetContents, hGetLine, hReady, hGetChar)
import System.Process     (runInteractiveProcess, waitForProcess, terminateProcess)

import qualified Data.Map.Strict as M
import qualified Data.Text       as T

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (SMTEngine, State(..), mustIgnoreVar)
import Data.SBV.Core.Concrete (showCV)
import Data.SBV.Core.Kind     (showBaseKind, intOfProxy)

import Data.SBV.Core.SizedFloats(FloatingPoint(..))

import Data.SBV.SMT.Utils     (showTimeoutValue, alignPlain, debug, mergeSExpr, SBVException(..))

import Data.SBV.Utils.PrettyNum
import Data.SBV.Utils.Lib       (joinArgs, splitArgs)
import Data.SBV.Utils.SExpr     (parenDeficit)
import Data.SBV.Utils.TDiff     (Timing(..), showTDiff)

import qualified System.Timeout as Timeout (timeout)

import Numeric

import qualified Data.SBV.Utils.CrackNum as CN

-- | Extract the final configuration from a result
resultConfig :: SMTResult -> SMTConfig
resultConfig (Unsatisfiable c _  ) = c
resultConfig (Satisfiable   c _  ) = c
resultConfig (DeltaSat      c _ _) = c
resultConfig (SatExtField   c _  ) = c
resultConfig (Unknown       c _  ) = c
resultConfig (ProofError    c _ _) = c

-- | A 'Data.SBV.prove' call results in a 'ThmResult'
newtype ThmResult = ThmResult SMTResult
                  deriving NFData

-- | A 'Data.SBV.sat' call results in a 'SatResult'
-- The reason for having a separate 'SatResult' is to have a more meaningful 'Show' instance.
newtype SatResult = SatResult SMTResult
                  deriving NFData

-- | An 'Data.SBV.allSat' call results in a 'AllSatResult'
data AllSatResult = AllSatResult { allSatMaxModelCountReached  :: Bool          -- ^ Did we reach the user given model count limit?
                                 , allSatSolverReturnedUnknown :: Bool          -- ^ Did the solver report unknown at the end?
                                 , allSatSolverReturnedDSat    :: Bool          -- ^ Did the solver report delta-satisfiable at the end?
                                 , allSatResults               :: [SMTResult]   -- ^ All satisfying models
                                 }

-- | A 'Data.SBV.safe' call results in a 'SafeResult'
newtype SafeResult   = SafeResult   (Maybe String, String, SMTResult)

-- | An 'Data.SBV.optimize' call results in a 'OptimizeResult'. In the 'ParetoResult' case, the boolean is 'True'
-- if we reached pareto-query limit and so there might be more unqueried results remaining. If 'False',
-- it means that we have all the pareto fronts returned. See the 'Pareto' 'OptimizeStyle' for details.
data OptimizeResult = LexicographicResult SMTResult
                    | ParetoResult        (Bool, [SMTResult])
                    | IndependentResult   [(String, SMTResult)]

-- | What's the precision of a delta-sat query?
getPrecision :: SMTResult -> Maybe String -> String
getPrecision r queriedPrecision = case (queriedPrecision, dsatPrecision (resultConfig r)) of
                                   (Just s, _     ) -> s
                                   (_,      Just d) -> showFFloat Nothing d ""
                                   _                -> "tool default"

-- User friendly way of printing theorem results
instance Show ThmResult where
  show (ThmResult r) = showSMTResult "Q.E.D."
                                     "Unknown"
                                     "Falsifiable"
                                     "Falsifiable. Counter-example:\n"
                                     (\mbP -> "Delta falsifiable, precision: " ++ getPrecision r mbP ++ ". Counter-example:\n")
                                     "Falsifiable in an extension field:\n"
                                     r

-- User friendly way of printing satisfiablity results
instance Show SatResult where
  show (SatResult r) = showSMTResult "Unsatisfiable"
                                     "Unknown"
                                     "Satisfiable"
                                     "Satisfiable. Model:\n"
                                     (\mbP -> "Delta satisfiable, precision: " ++ getPrecision r mbP ++ ". Model:\n")
                                     "Satisfiable in an extension field. Model:\n"
                                     r

-- User friendly way of printing safety results
instance Show SafeResult where
   show (SafeResult (mbLoc, msg, r)) = showSMTResult (tag "No violations detected")
                                                     (tag "Unknown")
                                                     (tag "Violated")
                                                     (tag "Violated. Model:\n")
                                                     (\mbP -> tag "Violated in a delta-satisfiable context, precision: " ++ getPrecision r mbP ++ ". Model:\n")
                                                     (tag "Violated in an extension field:\n")
                                                     r
        where loc   = maybe "" (++ ": ") mbLoc
              tag s = loc ++ msg ++ ": " ++ s

-- The Show instance of AllSatResults.
instance Show AllSatResult where
  show AllSatResult { allSatMaxModelCountReached  = l
                    , allSatSolverReturnedUnknown = u
                    , allSatSolverReturnedDSat    = d
                    , allSatResults               = xs
                    } = go (0::Int) xs
    where warnings | u    = " (Search stopped since solver has returned unknown.)"
                   | True = ""

          go c (s:ss) = let c'      = c+1
                            (ok, o) = sh c' s
                        in c' `seq` if ok then o ++ "\n" ++ go c' ss else o
          go c []     = case (l, d, c) of
                          (True,  _   , _) -> "Search stopped since model count request was reached."  ++ warnings
                          (_   ,  True, _) -> "Search stopped since the result was delta-satisfiable." ++ warnings
                          (False, _   , 0) -> "No solutions found."
                          (False, _   , 1) -> "This is the only solution." ++ warnings
                          (False, _   , _) -> "Found " ++ show c ++ " different solutions." ++ warnings

          sh i c = (ok, showSMTResult "Unsatisfiable"
                                      "Unknown"
                                      ("Solution #" ++ show i ++ ":\nSatisfiable") ("Solution #" ++ show i ++ ":\n")
                                      (\mbP -> "Solution $" ++ show i ++ " with delta-satisfiability, precision: " ++ getPrecision c mbP ++ ":\n")
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

               ParetoResult (False, [r]) -> sh ("Unique pareto front: " ++) r
               ParetoResult (False, rs)  -> multi "pareto optimal values" (zipWith shP [(1::Int)..] rs)
               ParetoResult (True,  rs)  ->    multi "pareto optimal values" (zipWith shP [(1::Int)..] rs)
                                           ++ "\n*** Note: Pareto-front extraction was terminated as requested by the user."
                                           ++ "\n***       There might be many other results!"

       where multi w [] = "There are no " ++ w ++ " to display models for."
             multi _ xs = intercalate "\n" xs

             shI n = sh (\s -> "Objective "     ++ show n ++ ": " ++ s)
             shP i = sh (\s -> "Pareto front #" ++ show i ++ ": " ++ s)

             sh tag r = showSMTResult (tag "Unsatisfiable.")
                                      (tag "Unknown.")
                                      (tag "Optimal with no assignments.")
                                      (tag "Optimal model:" ++ "\n")
                                      (\mbP -> tag "Optimal model with delta-satisfiability, precision: " ++ getPrecision r mbP ++ ":" ++ "\n")
                                      (tag "Optimal in an extension field:" ++ "\n")
                                      r

-- | Instances of 'SatModel' can be automatically extracted from models returned by the
-- solvers. The idea is that the sbv infrastructure provides a stream of CV's (constant values)
-- coming from the solver, and the type @a@ is interpreted based on these constants. Many typical
-- instances are already provided, so new instances can be declared with relative ease.
--
-- Minimum complete definition: 'parseCVs'
class SatModel a where
  -- | Given a sequence of constant-words, extract one instance of the type @a@, returning
  -- the remaining elements untouched. If the next element is not what's expected for this
  -- type you should return 'Nothing'
  parseCVs  :: [CV] -> Maybe (a, [CV])
  -- | Given a parsed model instance, transform it using @f@, and return the result.
  -- The default definition for this method should be sufficient in most use cases.
  cvtModel  :: (a -> Maybe b) -> Maybe (a, [CV]) -> Maybe (b, [CV])
  cvtModel f x = x >>= \(a, r) -> f a >>= \b -> return (b, r)

  default parseCVs :: Read a => [CV] -> Maybe (a, [CV])
  parseCVs (CV _ (CUserSort (_, s)) : r) = Just (read s, r)
  parseCVs _                             = Nothing

-- | Parse a signed/sized value from a sequence of CVs
genParse :: Integral a => Kind -> [CV] -> Maybe (a, [CV])
genParse k (x@(CV _ (CInteger i)):r) | kindOf x == k = Just (fromIntegral i, r)
genParse _ _                                         = Nothing

-- | Base case for 'SatModel' at unit type. Comes in handy if there are no real variables.
instance SatModel () where
  parseCVs xs = return ((), xs)

-- | 'Bool' as extracted from a model
instance SatModel Bool where
  parseCVs xs = do (x, r) <- genParse KBool xs
                   return ((x :: Integer) /= 0, r)

-- | 'Word8' as extracted from a model
instance SatModel Word8 where
  parseCVs = genParse (KBounded False 8)

-- | 'Int8' as extracted from a model
instance SatModel Int8 where
  parseCVs = genParse (KBounded True 8)

-- | 'Word16' as extracted from a model
instance SatModel Word16 where
  parseCVs = genParse (KBounded False 16)

-- | 'Int16' as extracted from a model
instance SatModel Int16 where
  parseCVs = genParse (KBounded True 16)

-- | 'Word32' as extracted from a model
instance SatModel Word32 where
  parseCVs = genParse (KBounded False 32)

-- | 'Int32' as extracted from a model
instance SatModel Int32 where
  parseCVs = genParse (KBounded True 32)

-- | 'Word64' as extracted from a model
instance SatModel Word64 where
  parseCVs = genParse (KBounded False 64)

-- | 'Int64' as extracted from a model
instance SatModel Int64 where
  parseCVs = genParse (KBounded True 64)

-- | 'Integer' as extracted from a model
instance SatModel Integer where
  parseCVs = genParse KUnbounded

-- | 'AlgReal' as extracted from a model
instance SatModel AlgReal where
  parseCVs (CV KReal (CAlgReal i) : r) = Just (i, r)
  parseCVs _                           = Nothing

-- | 'Float' as extracted from a model
instance SatModel Float where
  parseCVs (CV KFloat (CFloat i) : r) = Just (i, r)
  parseCVs _                          = Nothing

-- | 'Double' as extracted from a model
instance SatModel Double where
  parseCVs (CV KDouble (CDouble i) : r) = Just (i, r)
  parseCVs _                            = Nothing

-- | A general floating-point extracted from a model
instance (KnownNat eb, KnownNat sb) => SatModel (FloatingPoint eb sb) where
  parseCVs (CV (KFP ei si) (CFP fp) : r)
    | intOfProxy (Proxy @eb) == ei , intOfProxy (Proxy @sb) == si = Just (FloatingPoint fp, r)
  parseCVs _                                                      = Nothing

-- | @CV@ as extracted from a model; trivial definition
instance SatModel CV where
  parseCVs (cv : r) = Just (cv, r)
  parseCVs []       = Nothing

-- | A rounding mode, extracted from a model. (Default definition suffices)
instance SatModel RoundingMode

-- | 'String' as extracted from a model
instance {-# OVERLAPS #-} SatModel [Char] where
  parseCVs (CV _ (CString c):r) = Just (c, r)
  parseCVs _                    = Nothing

-- | 'Char' as extracted from a model
instance SatModel Char where
  parseCVs (CV _ (CChar c):r) = Just (c, r)
  parseCVs _                  = Nothing

-- | A list of values as extracted from a model. When reading a list, we
-- go as long as we can (maximal-munch). Note that this never fails, as
-- we can always return the empty list!
instance {-# OVERLAPPABLE #-} SatModel a => SatModel [a] where
  parseCVs [] = Just ([], [])
  parseCVs xs = case parseCVs xs of
                  Just (a, ys) -> case parseCVs ys of
                                    Just (as, zs) -> Just (a:as, zs)
                                    Nothing       -> Just ([], ys)
                  Nothing     -> Just ([], xs)

-- | Tuples extracted from a model
instance (SatModel a, SatModel b) => SatModel (a, b) where
  parseCVs as = do (a, bs) <- parseCVs as
                   (b, cs) <- parseCVs bs
                   return ((a, b), cs)

-- | 3-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c) => SatModel (a, b, c) where
  parseCVs as = do (a,      bs) <- parseCVs as
                   ((b, c), ds) <- parseCVs bs
                   return ((a, b, c), ds)

-- | 4-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d) => SatModel (a, b, c, d) where
  parseCVs as = do (a,         bs) <- parseCVs as
                   ((b, c, d), es) <- parseCVs bs
                   return ((a, b, c, d), es)

-- | 5-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e) => SatModel (a, b, c, d, e) where
  parseCVs as = do (a, bs)            <- parseCVs as
                   ((b, c, d, e), fs) <- parseCVs bs
                   return ((a, b, c, d, e), fs)

-- | 6-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f) => SatModel (a, b, c, d, e, f) where
  parseCVs as = do (a, bs)               <- parseCVs as
                   ((b, c, d, e, f), gs) <- parseCVs bs
                   return ((a, b, c, d, e, f), gs)

-- | 7-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f, SatModel g) => SatModel (a, b, c, d, e, f, g) where
  parseCVs as = do (a, bs)                  <- parseCVs as
                   ((b, c, d, e, f, g), hs) <- parseCVs bs
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
  getModelDictionary :: a -> M.Map String CV

  -- | Extract a model value for a given element. Also see `getModelValues`.
  getModelValue :: SymVal b => String -> a -> Maybe b
  getModelValue v r = fromCV `fmap` (v `M.lookup` getModelDictionary r)

  -- | Extract a representative name for the model value of an uninterpreted kind.
  -- This is supposed to correspond to the value as computed internally by the
  -- SMT solver; and is unportable from solver to solver. Also see `getModelUninterpretedValues`.
  getModelUninterpretedValue :: String -> a -> Maybe String
  getModelUninterpretedValue v r = case v `M.lookup` getModelDictionary r of
                                     Just (CV _ (CUserSort (_, s))) -> Just s
                                     _                              -> Nothing

  -- | A simpler variant of 'getModelAssignment' to get a model out without the fuss.
  extractModel :: SatModel b => a -> Maybe b
  extractModel a = case getModelAssignment a of
                     Right (_, b) -> Just b
                     _            -> Nothing

  -- | Extract model objective values, for all optimization goals.
  getModelObjectives :: a -> M.Map String GeneralizedCV

  -- | Extract the value of an objective
  getModelObjectiveValue :: String -> a -> Maybe GeneralizedCV
  getModelObjectiveValue v r = v `M.lookup` getModelObjectives r

  -- | Extract model uninterpreted-functions
  getModelUIFuns :: a -> M.Map String (Bool, SBVType, Either String ([([CV], CV)], CV))

  -- | Extract the value of an uninterpreted-function as an association list
  getModelUIFunValue :: String -> a -> Maybe (Bool, SBVType, Either String ([([CV], CV)], CV))
  getModelUIFunValue v r = v `M.lookup` getModelUIFuns r

-- | Return all the models from an 'Data.SBV.allSat' call, similar to 'extractModel' but
-- is suitable for the case of multiple results.
extractModels :: SatModel a => AllSatResult -> [a]
extractModels AllSatResult{allSatResults = xs} = [ms | Right (_, ms) <- map getModelAssignment xs]

-- | Get dictionaries from an all-sat call. Similar to `getModelDictionary`.
getModelDictionaries :: AllSatResult -> [M.Map String CV]
getModelDictionaries AllSatResult{allSatResults = xs} = map getModelDictionary xs

-- | Extract value of a variable from an all-sat call. Similar to `getModelValue`.
getModelValues :: SymVal b => String -> AllSatResult -> [Maybe b]
getModelValues s AllSatResult{allSatResults = xs} =  map (s `getModelValue`) xs

-- | Extract value of an uninterpreted variable from an all-sat call. Similar to `getModelUninterpretedValue`.
getModelUninterpretedValues :: String -> AllSatResult -> [Maybe String]
getModelUninterpretedValues s AllSatResult{allSatResults = xs} =  map (s `getModelUninterpretedValue`) xs

-- | 'ThmResult' as a generic model provider
instance Modelable ThmResult where
  getModelAssignment (ThmResult r) = getModelAssignment r
  modelExists        (ThmResult r) = modelExists        r
  getModelDictionary (ThmResult r) = getModelDictionary r
  getModelObjectives (ThmResult r) = getModelObjectives r
  getModelUIFuns     (ThmResult r) = getModelUIFuns     r

-- | 'SatResult' as a generic model provider
instance Modelable SatResult where
  getModelAssignment (SatResult r) = getModelAssignment r
  modelExists        (SatResult r) = modelExists        r
  getModelDictionary (SatResult r) = getModelDictionary r
  getModelObjectives (SatResult r) = getModelObjectives r
  getModelUIFuns     (SatResult r) = getModelUIFuns     r

-- | 'SMTResult' as a generic model provider
instance Modelable SMTResult where
  getModelAssignment (Unsatisfiable _ _  ) = Left "SBV.getModelAssignment: Unsatisfiable result"
  getModelAssignment (Satisfiable   _   m) = Right (False, parseModelOut m)
  getModelAssignment (DeltaSat      _ _ m) = Right (False, parseModelOut m)
  getModelAssignment (SatExtField   _ _  ) = Left "SBV.getModelAssignment: The model is in an extension field"
  getModelAssignment (Unknown       _ m  ) = Left $ "SBV.getModelAssignment: Solver state is unknown: " ++ show m
  getModelAssignment (ProofError    _ s _) = error $ unlines $ "SBV.getModelAssignment: Failed to produce a model: " : s

  modelExists Satisfiable{}   = True
  modelExists Unknown{}       = False -- don't risk it
  modelExists _               = False

  getModelDictionary Unsatisfiable{}     = M.empty
  getModelDictionary (Satisfiable _   m) = M.fromList (modelAssocs m)
  getModelDictionary (DeltaSat    _ _ m) = M.fromList (modelAssocs m)
  getModelDictionary SatExtField{}       = M.empty
  getModelDictionary Unknown{}           = M.empty
  getModelDictionary ProofError{}        = M.empty

  getModelObjectives Unsatisfiable{}     = M.empty
  getModelObjectives (Satisfiable _ m  ) = M.fromList (modelObjectives m)
  getModelObjectives (DeltaSat    _ _ m) = M.fromList (modelObjectives m)
  getModelObjectives (SatExtField _ m  ) = M.fromList (modelObjectives m)
  getModelObjectives Unknown{}           = M.empty
  getModelObjectives ProofError{}        = M.empty

  getModelUIFuns Unsatisfiable{}     = M.empty
  getModelUIFuns (Satisfiable _ m  ) = M.fromList (modelUIFuns m)
  getModelUIFuns (DeltaSat    _ _ m) = M.fromList (modelUIFuns m)
  getModelUIFuns (SatExtField _ m  ) = M.fromList (modelUIFuns m)
  getModelUIFuns Unknown{}           = M.empty
  getModelUIFuns ProofError{}        = M.empty

-- | Extract a model out, will throw error if parsing is unsuccessful
parseModelOut :: SatModel a => SMTModel -> a
parseModelOut m = case parseCVs [c | (_, c) <- modelAssocs m] of
                   Just (x, []) -> x
                   Just (_, ys) -> error $ "SBV.parseModelOut: Partially constructed model; remaining elements: " ++ show ys
                   Nothing      -> error $ "SBV.parseModelOut: Cannot construct a model from: " ++ show m

-- | Given an 'Data.SBV.allSat' call, we typically want to iterate over it and print the results in sequence. The
-- 'displayModels' function automates this task by calling @disp@ on each result, consecutively. The first
-- 'Int' argument to @disp@ 'is the current model number. The second argument is a tuple, where the first
-- element indicates whether the model is alleged (i.e., if the solver is not sure, returning Unknown).
-- The arrange argument can sort the results in any way you like, if necessary.
displayModels :: SatModel a => ([(Bool, a)] -> [(Bool, a)]) -> (Int -> (Bool, a) -> IO ()) -> AllSatResult -> IO Int
displayModels arrange disp AllSatResult{allSatResults = ms} = do
    let models = rights (map (getModelAssignment . SatResult) ms)
    inds <- zipWithM display (arrange models) [(1::Int)..]
    return $ last (0:inds)
  where display r i = disp i r >> return i

-- | Show an SMTResult; generic version
showSMTResult :: String -> String -> String -> String -> (Maybe String -> String) -> String -> SMTResult -> String
showSMTResult unsatMsg unkMsg satMsg satMsgModel dSatMsgModel satExtMsg result = case result of
  Unsatisfiable _ uc                 -> unsatMsg ++ showUnsatCore uc
  Satisfiable _ (SMTModel _ _ [] []) -> satMsg
  Satisfiable _   m                  -> satMsgModel    ++ showModel cfg m
  DeltaSat    _ p m                  -> dSatMsgModel p ++ showModel cfg m
  SatExtField _ (SMTModel b _ _ _)   -> satExtMsg   ++ showModelDictionary True False cfg b
  Unknown     _ r                    -> unkMsg ++ ".\n" ++ "  Reason: " `alignPlain` show r
  ProofError  _ [] Nothing           -> "*** An error occurred. No additional information available. Try running in verbose mode."
  ProofError  _ ls Nothing           -> "*** An error occurred.\n" ++ intercalate "\n" (map ("***  " ++) ls)
  ProofError  _ ls (Just r)          -> intercalate "\n" $  [ "*** " ++ l | l <- ls]
                                                         ++ [ "***"
                                                            , "*** Alleged model:"
                                                            , "***"
                                                            ]
                                                         ++ ["*** "  ++ l | l <- lines (showSMTResult unsatMsg unkMsg satMsg satMsgModel dSatMsgModel satExtMsg r)]

 where cfg = resultConfig result
       showUnsatCore Nothing   = ""
       showUnsatCore (Just xs) = ". Unsat core:\n" ++ intercalate "\n" ["    " ++ x | x <- xs]

-- | Show a model in human readable form. Ignore bindings to those variables that start
-- with "__internal_sbv_" and also those marked as "nonModelVar" in the config; as these are only for internal purposes
showModel :: SMTConfig -> SMTModel -> String
showModel cfg model
   | null uiFuncs
   = nonUIFuncs
   | True
   = sep nonUIFuncs ++ intercalate "\n\n" (map (showModelUI cfg) uiFuncs)
   where nonUIFuncs = showModelDictionary (null uiFuncs) False cfg [(n, RegularCV c) | (n, c) <- modelAssocs model]
         uiFuncs    = modelUIFuns model
         sep ""     = ""
         sep x      = x ++ "\n\n"

-- | Show bindings in a generalized model dictionary, tabulated
showModelDictionary :: Bool -> Bool -> SMTConfig -> [(String, GeneralizedCV)] -> String
showModelDictionary warnEmpty includeEverything cfg allVars
   | null allVars
   = warn "[There are no variables bound by the model.]"
   | null relevantVars
   = warn "[There are no model-variables bound by the model.]"
   | True
   = intercalate "\n" . display . map shM $ relevantVars
  where warn s = if warnEmpty then s else ""

        relevantVars  = filter (not . ignore) allVars
        ignore (T.pack -> s, _)
          | includeEverything = False
          | True              = mustIgnoreVar cfg (T.unpack s)

        shM (s, RegularCV v) = let vs = shCV cfg s v in ((length s, s), (vlength vs, vs))
        shM (s, other)       = let vs = show other   in ((length s, s), (vlength vs, vs))

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

-- | Show an uninterpreted function
showModelUI :: SMTConfig -> (String, (Bool, SBVType, Either String ([([CV], CV)], CV))) -> String
showModelUI cfg (nm, (isCurried, SBVType ts, interp))
  = intercalate "\n" $ case interp of
                         Left  e  -> ["  " ++ l | l <- [sig, e]]
                         Right ds -> ["  " ++ l | l <- sig : mkBody ds]
  where noOfArgs = length ts - 1

        (ats, rt) = case map showBaseKind ts of
                     []  -> error $ "showModelUI: Unexpected type: " ++ show (SBVType ts)
                     tss -> (init tss, last tss)

        sig | isCurried = nm ++ " :: "  ++ intercalate " -> " ats ++  " -> " ++ rt
            | True      = nm ++ " :: (" ++ intercalate ", "   ats ++ ") -> " ++ rt

        mkBody (defs, dflt) = map align body
          where ls       = map line defs
                defLine  = (replicate noOfArgs "_", scv dflt)
                body     = ls ++ [defLine]

                colWidths = [maximum (0 : map length col) | col <- transpose (map fst body)]

                resWidth  = maximum  (0 : map (length . snd) body)

                align (xs, r) = nm ++ " " ++ merge (zipWith left colWidths xs) ++ " = " ++ left resWidth r
                   where left i x = take i (x ++ repeat ' ')

                         merge as | isCurried = unwords as
                                  | True      = '(' : intercalate ", " as ++ ")"

        -- NB. We'll ignore crackNum here. Seems to be overkill while displaying an
        -- uninterpreted function.
        scv = sh (printBase cfg)
          where sh 2  = binP
                sh 10 = showCV False
                sh 16 = hexP
                sh _  = show

        -- NB. If we have a float NaN/Infinity/+0/-0 etc. these will
        -- simply print as is, but will not be valid patterns. (We
        -- have the semi-goal of being able to paste these definitions
        -- in a Haskell file.) For the time being, punt on this, but
        -- we might want to do this properly later somehow. (Perhaps
        -- using some sort of a view pattern.)
        line :: ([CV], CV) -> ([String], String)
        line (args, r) = (map (paren isCurried . scv) args, scv r)
          where -- If negative and if we're curried, parenthesize. I think this is the only case
                -- we need to worry about. Hopefully!
                paren :: Bool -> String -> String
                paren True x@('-':_) = '(' : x ++ ")"
                paren _    x         = x

-- | Show a constant value, in the user-specified base
shCV :: SMTConfig -> String -> CV -> String
shCV SMTConfig{printBase, crackNum, verbose, crackNumSurfaceVals} nm cv = cracked (sh printBase cv)
  where sh 2  = binS
        sh 10 = show
        sh 16 = hexS
        sh n  = \w -> show w ++ " -- Ignoring unsupported printBase " ++ show n ++ ", use 2, 10, or 16."

        cracked def
          | not crackNum = def
          | True         = case CN.crackNum cv verbose (nm `lookup` crackNumSurfaceVals) of
                             Nothing -> def
                             Just cs -> def ++ "\n" ++ cs

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
                        [ C.Handler (\(e :: SBVException)    -> C.throwIO e)
                        , C.Handler (\(e :: C.ErrorCall)     -> C.throwIO e)
                        , C.Handler (\(e :: C.SomeException) -> handleAsync e $ error $ unlines [ "Failed to start the external solver:\n" ++ show e
                                                                                                , "Make sure you can start " ++ show execPath
                                                                                                , "from the command line without issues."
                                                                                                ])
                        ]

-- | A standard engine interface. Most solvers follow-suit here in how we "chat" to them..
standardEngine :: String
               -> String
               -> SMTEngine
standardEngine envName envOptName cfg ctx pgm continuation = do

    execName <-                    getEnv envName     `C.catch` (\(e :: C.SomeException) -> handleAsync e (return (executable (solver cfg))))
    execOpts <- (splitArgs `fmap`  getEnv envOptName) `C.catch` (\(e :: C.SomeException) -> handleAsync e (return (options (solver cfg) cfg)))

    let cfg' = cfg {solver = (solver cfg) {executable = execName, options = const execOpts}}

    standardSolver cfg' ctx pgm continuation

-- | A standard solver interface. If the solver is SMT-Lib compliant, then this function should suffice in
-- communicating with it.
standardSolver :: SMTConfig       -- ^ The current configuration
               -> State           -- ^ Context in which we are running
               -> String          -- ^ The program
               -> (State -> IO a) -- ^ The continuation
               -> IO a
standardSolver config ctx pgm continuation = do
    let msg s    = debug config ["** " ++ s]
        smtSolver= solver config
        exec     = executable smtSolver
        opts     = options smtSolver config ++ extraArgs config
    msg $ "Calling: "  ++ (exec ++ (if null opts then "" else " ") ++ joinArgs opts)
    rnf pgm `seq` pipeProcess config ctx exec opts pgm continuation

-- | An internal type to track of solver interactions
data SolverLine = SolverRegular   String -- ^ All is well
                | SolverTimeout   String -- ^ Timeout expired
                | SolverException String -- ^ Something else went wrong

-- | A variant of @readProcessWithExitCode@; except it deals with SBV continuations
runSolver :: SMTConfig -> State -> FilePath -> [String] -> String -> (State -> IO a) -> IO a
runSolver cfg ctx execPath opts pgm continuation
 = do let nm  = show (name (solver cfg))
          msg = debug cfg . map ("*** " ++)

          clean = preprocess (solver cfg)

          -- the very first command we send
          heartbeat = "(set-option :print-success true)"

      (send, ask, getResponseFromSolver, terminateSolver, cleanUp, pid) <- do
                (inh, outh, errh, pid) <- runInteractiveProcess execPath opts Nothing Nothing

                let send :: Maybe Int -> String -> IO ()
                    send mbTimeOut command = do hPutStrLn inh (clean command)
                                                hFlush inh
                                                recordTranscript (transcript cfg) $ Left (command, mbTimeOut)

                    -- is this a set-command? Then we expect faster response; except for the heartbeat
                    isSetCommand = maybe False chk
                      where chk cmd = cmd /= heartbeat && "(set-option :" `isPrefixOf` cmd

                    -- Send a line, get a whole s-expr. We ignore the pathetic case that there might be a string with an unbalanced parentheses in it in a response.
                    ask :: Maybe Int -> String -> IO String
                    ask mbTimeOutGiven command =
                                  let -- If the command is a set-option call, make sure there's a timeout on it
                                      -- This ensures that if we try to set an option before diagnostic-output
                                      -- is redirected to stdout and the solver chokes, then we can catch it
                                      mbTimeOut | isSetCommand (Just command) = Just 1000000
                                                | True                        = mbTimeOutGiven

                                      -- solvers don't respond to empty lines or comments; we just pass back
                                      -- success in these cases to keep the illusion of everything has a response
                                      cmd = dropWhile isSpace command

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
                                         let timeOutToUse | isSetCommand mbCommand = Just 2000000
                                                          | isFirst                = mbTimeOut
                                                          | True                   = Just 5000000
                                             timeOutMsg t | isFirst = "User specified timeout of " ++ showTimeoutValue t ++ " exceeded"
                                                          | True    = "A multiline complete response wasn't received before " ++ showTimeoutValue t ++ " exceeded"

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

                                             -- Carefully grab things as they are ready. But don't block!
                                             collectH handle = reverse <$> coll ""
                                               where coll sofar = do b <- hReady handle
                                                                     if b
                                                                        then hGetChar handle >>= \c -> coll (c:sofar)
                                                                        else pure sofar

                                             -- grab the contents of a handle, and return it trimmed if any
                                             grab handle = do mbCts <- (Just <$> collectH handle) `C.catch` (\(_ :: C.SomeException) -> pure Nothing)
                                                              pure $ dropWhile isSpace <$> mbCts

                                         in case timeOutToUse of
                                              Nothing -> SolverRegular <$> getFullLine
                                              Just t  -> do r <- Timeout.timeout t getFullLine
                                                            case r of
                                                              Just l  -> return $ SolverRegular l
                                                              Nothing -> do out <- grab outh
                                                                            err <- grab errh
                                                                            -- in this case, if we have something on out/err pass that back as regular
                                                                            case err `mplus` out of
                                                                              Just x | not (null x) -> pure $ SolverRegular x
                                                                              _                     -> pure $ SolverTimeout (timeOutMsg t)

                            go isFirst i sofar = do
                                            errln <- safeGetLine isFirst outh `C.catch` (\(e :: C.SomeException) -> handleAsync e (return (SolverException (show e))))
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

                                              SolverException e -> do terminateProcess pid
                                                                      C.throwIO SBVException { sbvExceptionDescription = e
                                                                                             , sbvExceptionSent        = mbCommand
                                                                                             , sbvExceptionExpected    = Nothing
                                                                                             , sbvExceptionReceived    = Just $ unlines (reverse sofar)
                                                                                             , sbvExceptionStdOut      = Nothing
                                                                                             , sbvExceptionStdErr      = Nothing
                                                                                             , sbvExceptionExitCode    = Nothing
                                                                                             , sbvExceptionConfig      = cfg { solver = (solver cfg) { executable = execPath } }
                                                                                             , sbvExceptionReason      = Nothing
                                                                                             , sbvExceptionHint        = if "hGetLine: end of file" `isInfixOf` e
                                                                                                                         then Just [ "Solver process prematurely ended communication."
                                                                                                                                   , ""
                                                                                                                                   , "It is likely it was terminated because of a seg-fault."
                                                                                                                                   , "Run with 'transcript=Just \"bad.smt2\"' option, and feed"
                                                                                                                                   , "the generated \"bad.smt2\" file directly to the solver"
                                                                                                                                   , "outside of SBV for further information."
                                                                                                                                   ]
                                                                                                                         else Nothing
                                                                                             }

                                              SolverTimeout e -> do terminateProcess pid -- NB. Do not *wait* for the process, just quit.

                                                                    C.throwIO SBVException { sbvExceptionDescription = "Timeout! " ++ e
                                                                                           , sbvExceptionSent        = mbCommand
                                                                                           , sbvExceptionExpected    = Nothing
                                                                                           , sbvExceptionReceived    = Just $ unlines (reverse sofar)
                                                                                           , sbvExceptionStdOut      = Nothing
                                                                                           , sbvExceptionStdErr      = Nothing
                                                                                           , sbvExceptionExitCode    = Nothing
                                                                                           , sbvExceptionConfig      = cfg { solver = (solver cfg) { executable = execPath } }
                                                                                           , sbvExceptionReason      = Nothing
                                                                                           , sbvExceptionHint        = if not (verbose cfg)
                                                                                                                       then Just ["Run with 'verbose=True' for further information"]
                                                                                                                       else Nothing
                                                                                           }

                    terminateSolver = do hClose inh
                                         outMVar <- newEmptyMVar
                                         out <- hGetContents outh `C.catch`  (\(e :: C.SomeException) -> handleAsync e (return (show e)))
                                         _ <- forkIO $ C.evaluate (length out) >> putMVar outMVar ()
                                         err <- hGetContents errh `C.catch`  (\(e :: C.SomeException) -> handleAsync e (return (show e)))
                                         _ <- forkIO $ C.evaluate (length err) >> putMVar outMVar ()
                                         takeMVar outMVar
                                         takeMVar outMVar
                                         hClose outh `C.catch`  (\(e :: C.SomeException) -> handleAsync e (return ()))
                                         hClose errh `C.catch`  (\(e :: C.SomeException) -> handleAsync e (return ()))
                                         ex <- waitForProcess pid `C.catch` (\(e :: C.SomeException) -> handleAsync e (return (ExitFailure (-999))))
                                         return (out, err, ex)

                    cleanUp
                      = do (out, err, ex) <- terminateSolver

                           msg $   [ "Solver   : " ++ nm
                                   , "Exit code: " ++ show ex
                                   ]
                                ++ [ "Std-out  : " ++ intercalate "\n           " (lines out) | not (null out)]
                                ++ [ "Std-err  : " ++ intercalate "\n           " (lines err) | not (null err)]

                           finalizeTranscript (transcript cfg) ex
                           recordEndTime cfg ctx

                           case ex of
                             ExitSuccess -> return ()
                             _           -> if ignoreExitCode cfg
                                               then msg ["Ignoring non-zero exit code of " ++ show ex ++ " per user request!"]
                                               else C.throwIO SBVException { sbvExceptionDescription = "Failed to complete the call to " ++ nm
                                                                           , sbvExceptionSent        = Nothing
                                                                           , sbvExceptionExpected    = Nothing
                                                                           , sbvExceptionReceived    = Nothing
                                                                           , sbvExceptionStdOut      = Just out
                                                                           , sbvExceptionStdErr      = Just err
                                                                           , sbvExceptionExitCode    = Just ex
                                                                           , sbvExceptionConfig      = cfg { solver = (solver cfg) { executable = execPath } }
                                                                           , sbvExceptionReason      = Nothing
                                                                           , sbvExceptionHint        = if not (verbose cfg)
                                                                                                       then Just ["Run with 'verbose=True' for further information"]
                                                                                                       else Nothing
                                                                           }

                return (send, ask, getResponseFromSolver, terminateSolver, cleanUp, pid)

      let executeSolver = do let sendAndGetSuccess :: Maybe Int -> String -> IO ()
                                 sendAndGetSuccess mbTimeOut l
                                   -- The pathetic case when the solver doesn't support queries, so we pretend it responded "success"
                                   -- Currently ABC is the only such solver.
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
                                                            mbExtras <- (Right <$> getResponseFromSolver Nothing (Just 5000000))
                                                                        `C.catch` (\(e :: C.SomeException) -> handleAsync e (return (Left (show e))))

                                                            -- Ignore any exceptions from last sync, pointless.
                                                            let extras = case mbExtras of
                                                                           Left _   -> []
                                                                           Right xs -> xs

                                                            (outOrig, errOrig, ex) <- terminateSolver
                                                            let out = intercalate "\n" . lines $ outOrig
                                                                err = intercalate "\n" . lines $ errOrig

                                                                exc = SBVException { sbvExceptionDescription = "Unexpected non-success response from " ++ nm
                                                                                   , sbvExceptionSent        = Just l
                                                                                   , sbvExceptionExpected    = Just "success"
                                                                                   , sbvExceptionReceived    = Just $ r ++ "\n" ++ extras
                                                                                   , sbvExceptionStdOut      = Just out
                                                                                   , sbvExceptionStdErr      = Just err
                                                                                   , sbvExceptionExitCode    = Just ex
                                                                                   , sbvExceptionConfig      = cfg { solver = (solver cfg) {executable = execPath } }
                                                                                   , sbvExceptionReason      = Just reason
                                                                                   , sbvExceptionHint        = Nothing
                                                                                   }

                                                            C.throwIO exc

                             -- Mark in the log, mostly.
                             sendAndGetSuccess Nothing "; Automatically generated by SBV. Do not edit."

                             -- First check that the solver supports :print-success
                             let backend = name $ solver cfg
                             if not (supportsCustomQueries (capabilities (solver cfg)))
                                then debug cfg ["** Skipping heart-beat for the solver " ++ show backend]
                                else do r <- ask (Just 5000000) heartbeat  -- Give the solver 5s to respond, this should be plenty enough!
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
                                                 }
                                 qsp = rQueryState ctx

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
      let launchSolver = do startTranscript (transcript cfg) cfg
                            executeSolver

      launchSolver `C.catch` (\(e :: C.SomeException) -> handleAsync e $ do terminateProcess pid
                                                                            ec <- waitForProcess pid
                                                                            recordException    (transcript cfg) (show e)
                                                                            finalizeTranscript (transcript cfg) ec
                                                                            recordEndTime cfg ctx
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
                                  , ";;;           Options   : " ++ unwords (options cfg ++ extraArgs cfg)
                                  , ";;;"
                                  , ";;; This file is an auto-generated loadable SMT-Lib file."
                                  , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                                  , ""
                                  ]

-- | Finish up the transcript file.
finalizeTranscript :: Maybe FilePath -> ExitCode -> IO ()
finalizeTranscript Nothing  _  = return ()
finalizeTranscript (Just f) ec = do ts <- show <$> getZonedTime
                                    appendFile f $ end ts
  where end ts = unlines [ ""
                         , ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
                         , ";;;"
                         , ";;; SBV: Finished at " ++ ts
                         , ";;;"
                         , ";;; Exit code: " ++ show ec
                         , ";;;"
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

-- We should not be catching/processing asynchronous exceptions.
-- See http://github.com/LeventErkok/sbv/issues/410
handleAsync :: C.SomeException -> IO a -> IO a
handleAsync e cont
  | isAsynchronous = C.throwIO e
  | True           = cont
  where -- Stealing this definition from the asynchronous exceptions package to reduce dependencies
        isAsynchronous :: Bool
        isAsynchronous = isJust (C.fromException e :: Maybe C.AsyncException) || isJust (C.fromException e :: Maybe C.SomeAsyncException)
