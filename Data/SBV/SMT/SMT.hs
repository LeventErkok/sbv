-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Abstraction of SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.SMT.SMT where

import Control.DeepSeq  (NFData(..))
import Control.Monad    (when, zipWithM)
import Data.Char        (isSpace)
import Data.Int         (Int8, Int16, Int32, Int64)
import Data.List        (intercalate)
import Data.Word        (Word8, Word16, Word32, Word64)
import System.Directory (findExecutable)
import System.Process   (readProcessWithExitCode)
import System.Exit      (ExitCode(..))

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum
import Data.SBV.Utils.TDiff

-- | Solver configuration
data SMTConfig = SMTConfig {
         verbose   :: Bool      -- ^ Debug mode
       , timing    :: Bool      -- ^ Print timing information on how long different phases took (construction, solving, etc.)
       , printBase :: Int       -- ^ Print literals in this base
       , solver    :: SMTSolver -- ^ The actual SMT solver
       }

type SMTEngine = SMTConfig -> [NamedSymVar] -> [(String, UnintKind)] -> String -> IO SMTResult

-- | An SMT solver
data SMTSolver = SMTSolver {
         name       :: String    -- ^ Printable name of the solver
       , executable :: String    -- ^ The path to its executable
       , options    :: [String]  -- ^ Options to provide to the solver
       , engine     :: SMTEngine -- ^ The solver engine, responsible for interpreting solver output
       }

-- | A model, as returned by a solver
data SMTModel = SMTModel {
        modelAssocs    :: [(String, CW)]
     ,  modelArrays    :: [(String, [String])]  -- very crude!
     ,  modelUninterps :: [(String, [String])]  -- very crude!
     }
     deriving Show

-- | The result of an SMT solver call. Each constructor is tagged with
-- the 'SMTConfig' that created it so that further tools can inspect it
-- and build layers of results, if needed. For ordinary uses of the library,
-- this type should not be needed, instead use the accessor functions on
-- it. (Custom Show instances and model extractors.)
data SMTResult = Unsatisfiable SMTConfig            -- ^ Unsatisfiable
               | Satisfiable   SMTConfig SMTModel   -- ^ Satisfiable with model
               | Unknown       SMTConfig SMTModel   -- ^ Prover returned unknown, with a potential (possibly bogus) model
               | ProofError    SMTConfig [String]   -- ^ Prover errored out
               | TimeOut       SMTConfig            -- ^ Computation timed out (see the 'timeout' combinator)

resultConfig :: SMTResult -> SMTConfig
resultConfig (Unsatisfiable c) = c
resultConfig (Satisfiable c _) = c
resultConfig (Unknown c _)     = c
resultConfig (ProofError c _)  = c
resultConfig (TimeOut c)       = c

instance NFData SMTResult where
  rnf (Unsatisfiable _)   = ()
  rnf (Satisfiable _ xs)  = rnf xs `seq` ()
  rnf (Unknown _ xs)      = rnf xs `seq` ()
  rnf (ProofError _ xs)   = rnf xs `seq` ()
  rnf (TimeOut _)         = ()

instance NFData SMTModel where
  rnf (SMTModel assocs unints uarrs) = rnf assocs `seq` rnf unints `seq` rnf uarrs `seq` ()

-- | A 'prove' call results in a 'ThmResult'
newtype ThmResult    = ThmResult    SMTResult

-- | A 'sat' call results in a 'SatResult'
-- The reason for having a separate 'SatResult' is to have a more meaningful 'Show' instance.
newtype SatResult    = SatResult    SMTResult

-- | An 'allSat' call results in a 'AllSatResult'
newtype AllSatResult = AllSatResult [SMTResult]

instance Show ThmResult where
  show (ThmResult r) = showSMTResult "Q.E.D."
                                     "Unknown"     "Unknown. Potential counter-example:\n"
                                     "Falsifiable" "Falsifiable. Counter-example:\n" r

instance Show SatResult where
  show (SatResult r) = showSMTResult "Unsatisfiable"
                                     "Unknown"     "Unknown. Potential model:\n"
                                     "Satisfiable" "Satisfiable. Model:\n" r


instance Show AllSatResult where
  show (AllSatResult [])  =  "No solutions found"
  show (AllSatResult [s]) =  "Only one solution found:\n" ++ shUnique s
        where shUnique = showSMTResult "Unsatisfiable"
                                       ("Unknown (No assignment to variables returned)") "Unknown. Potential assignment:\n" "" ""
  show (AllSatResult ss)  =  "Multiple solutions found:\n"      -- shouldn't display how-many; would be too slow/leak-space to compute everything..
                          ++ unlines (zipWith sh [(1::Int)..] ss)
                          ++ "Done."
        where sh i = showSMTResult "Unsatisfiable"
                                   ("Unknown #" ++ show i ++ "(No assignment to variables returned)") "Unknown. Potential assignment:\n"
                                   ("Solution #" ++ show i ++ " (No assignment to variables returned)") ("Solution #" ++ show i ++ ":\n")

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

genParse :: Integral a => (Bool,Size) -> [CW] -> Maybe (a,[CW])
genParse (signed,size) (x:r)
  | hasSign x == signed && sizeOf x == size = Just (fromIntegral (cwVal x),r)
genParse _ _ = Nothing

instance SatModel Bool where
  parseCWs xs = do (x,r) <- genParse (False,1) xs
                   return ((x :: Integer) /= 0, r)

instance SatModel Word8 where
  parseCWs = genParse (False,8)

instance SatModel Int8 where
  parseCWs = genParse (True,8)

instance SatModel Word16 where
  parseCWs = genParse (False,16)

instance SatModel Int16 where
  parseCWs = genParse (True,16)

instance SatModel Word32 where
  parseCWs = genParse (False,32)

instance SatModel Int32 where
  parseCWs = genParse (True,32)

instance SatModel Word64 where
  parseCWs = genParse (False,64)

instance SatModel Int64 where
  parseCWs = genParse (True,64)

-- when reading a list; go as long as we can (maximal-munch)
-- note that this never fails..
instance SatModel a => SatModel [a] where
  parseCWs [] = Just ([], [])
  parseCWs xs = case parseCWs xs of
                  Just (a, ys) -> case parseCWs ys of
                                    Just (as, zs) -> Just (a:as, zs)
                                    Nothing       -> Just ([], ys)
                  Nothing     -> Just ([], xs)

instance (SatModel a, SatModel b) => SatModel (a, b) where
  parseCWs as = do (a, bs) <- parseCWs as
                   (b, cs) <- parseCWs bs
                   return ((a, b), cs)

instance (SatModel a, SatModel b, SatModel c) => SatModel (a, b, c) where
  parseCWs as = do (a,      bs) <- parseCWs as
                   ((b, c), ds) <- parseCWs bs
                   return ((a, b, c), ds)

instance (SatModel a, SatModel b, SatModel c, SatModel d) => SatModel (a, b, c, d) where
  parseCWs as = do (a,         bs) <- parseCWs as
                   ((b, c, d), es) <- parseCWs bs
                   return ((a, b, c, d), es)

instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e) => SatModel (a, b, c, d, e) where
  parseCWs as = do (a, bs)            <- parseCWs as
                   ((b, c, d, e), fs) <- parseCWs bs
                   return ((a, b, c, d, e), fs)

instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f) => SatModel (a, b, c, d, e, f) where
  parseCWs as = do (a, bs)               <- parseCWs as
                   ((b, c, d, e, f), gs) <- parseCWs bs
                   return ((a, b, c, d, e, f), gs)

instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f, SatModel g) => SatModel (a, b, c, d, e, f, g) where
  parseCWs as = do (a, bs)                  <- parseCWs as
                   ((b, c, d, e, f, g), hs) <- parseCWs bs
                   return ((a, b, c, d, e, f, g), hs)

-- | Given an 'SMTResult', extract an arbitrarily typed model from it, given a 'SatModel' instance
getModel :: SatModel a => SMTResult -> a
getModel (Unsatisfiable _) = error "SatModel.getModel: Unsatisfiable result"
getModel (Unknown _ _)     = error "Impossible! Backend solver returned unknown for Bit-vector problem!"
getModel (ProofError _ s)  = error $ unlines $ "An error happened: " : s
getModel (TimeOut _)       = error $ "Timeout"
getModel (Satisfiable _ m) = case parseCWs [c | (_, c) <- modelAssocs m] of
                               Just (x, []) -> x
                               Just (_, ys) -> error $ "SBV.getModel: Partially constructed model; remaining elements: " ++ show ys
                               Nothing      -> error $ "SBV.getModel: Cannot construct a model from: " ++ show m

-- | Given an 'allSat' call, we typically want to iterate over it and print the results in sequence. The
-- 'displayModels' function automates this task by calling 'disp' on each result, consecutively. The first
-- 'Int' argument to 'disp' 'is the current model number.
displayModels :: SatModel a => (Int -> a -> IO ()) -> AllSatResult -> IO Int
displayModels disp (AllSatResult ms) = do
    inds <- zipWithM display (map getModel ms) [(1::Int)..]
    return $ last (0:inds)
  where display r i = disp i r >> return i

showSMTResult :: String -> String -> String -> String -> String -> SMTResult -> String
showSMTResult unsatMsg unkMsg unkMsgModel satMsg satMsgModel result = case result of
  Unsatisfiable _                   -> unsatMsg
  Satisfiable _ (SMTModel [] [] []) -> satMsg
  Satisfiable _ m                   -> satMsgModel ++ showModel cfg m
  Unknown _ (SMTModel [] [] [])     -> unkMsg
  Unknown _ m                       -> unkMsgModel ++ showModel cfg m
  ProofError _ []                   -> "*** An error occurred. No additional information available. Try running in verbose mode"
  ProofError _ ls                   -> "*** An error occurred.\n" ++ intercalate "\n" (map ("***  " ++) ls)
  TimeOut _                         -> "*** Timeout"
 where cfg = resultConfig result

showModel :: SMTConfig -> SMTModel -> String
showModel cfg m = intercalate "\n" (map (shM cfg) assocs ++ concatMap shUI uninterps ++ concatMap shUA arrs)
  where assocs    = modelAssocs m
        uninterps = modelUninterps m
        arrs      = modelArrays m

shCW :: SMTConfig -> CW -> String
shCW cfg v = sh (printBase cfg) v
  where sh 2  = binS
        sh 10 = show
        sh 16 = hexS
        sh n  = \w -> show w ++ " -- Ignoring unsupported printBase " ++ show n ++ ", use 2, 10, or 16."

shM :: SMTConfig -> (String, CW) -> String
shM cfg (s, v) = "  " ++ s ++ " = " ++ shCW cfg v

-- very crude.. printing uninterpreted functions
shUI :: (String, [String]) -> [String]
shUI (flong, cases) = ("  -- uninterpreted: " ++ f) : map shC cases
  where tf = dropWhile (/= '_') flong
        f  =  if null tf then flong else tail tf
        shC s = "       " ++ s

-- very crude.. printing array values
shUA :: (String, [String]) -> [String]
shUA (f, cases) = ("  -- array: " ++ f) : map shC cases
  where shC s = "       " ++ s

pipeProcess :: String -> String -> [String] -> String -> IO (Either String [String])
pipeProcess nm execName opts script = do
        mbExecPath <- findExecutable execName
        case mbExecPath of
          Nothing -> return $ Left $ "Unable to locate executable for " ++ nm
                                   ++ "\nExecutable specified: " ++ show execName
          Just execPath -> do (ec, contents, errors) <- readProcessWithExitCode execPath opts script
                              case ec of
                                ExitSuccess  ->  if null errors
                                                 then return $ Right $ map clean (filter (not . null) (lines contents))
                                                 else return $ Left errors
                                ExitFailure n -> let errors' = if null (dropWhile isSpace errors)
                                                               then (if null (dropWhile isSpace contents)
                                                                     then "(No error message printed on stderr by the executable.)"
                                                                     else contents)
                                                               else errors
                                                 in return $ Left $  "Failed to complete the call to " ++ nm
                                                                  ++ "\nExecutable   : " ++ show execPath
                                                                  ++ "\nOptions      : " ++ unwords opts
                                                                  ++ "\nExit code    : " ++ show n
                                                                  ++ "\nSolver output: "
                                                                  ++ "\n" ++ line ++ "\n"
                                                                  ++ intercalate "\n" (filter (not . null) (lines errors'))
                                                                  ++ "\n" ++ line
                                                                  ++ "\nGiving up.."
  where clean = reverse . dropWhile isSpace . reverse . dropWhile isSpace
        line  = take 78 $ repeat '='

standardSolver :: SMTConfig -> String -> ([String] -> a) -> ([String] -> a) -> IO a
standardSolver config script failure success = do
    let msg      = when (verbose config) . putStrLn . ("** " ++)
        smtSolver= solver config
        exec     = executable smtSolver
        opts     = options smtSolver
        isTiming = timing config
        nmSolver = name smtSolver
    msg $ "Calling: " ++ show (unwords (exec:opts))
    contents <- timeIf isTiming nmSolver $ pipeProcess nmSolver exec opts script
    msg $ nmSolver ++ " output:\n" ++ either id (intercalate "\n") contents
    case contents of
      Left e   -> return $ failure (lines e)
      Right xs -> return $ success xs
