-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Prover
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Provable abstraction and the connection to SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate, Provable(..)
       , ThmResult(..), SatResult(..), SafeResult(..), AllSatResult(..), SMTResult(..)
       , isSatisfiable, isSatisfiableWith, isTheorem, isTheoremWith
       , prove, proveWith
       , sat, satWith
       , safe, safeWith, isSafe
       , allSat, allSatWith
       , isVacuous, isVacuousWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , boolector, cvc4, yices, z3, mathSAT, abc, defaultSMTCfg
       , compileToSMTLib, generateSMTBenchmarks
       , internalSATCheck
       ) where

import Control.Monad    (when, unless)
import Data.List        (intercalate)
import System.FilePath  (addExtension, splitExtension)
import System.Time      (getClockTime)
import System.IO.Unsafe (unsafeInterleaveIO)

import GHC.Stack.Compat
import GHC.SrcLoc.Compat

import qualified Data.Set as Set (Set, toList)

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.Utils.TDiff

import qualified Data.SBV.Provers.Boolector  as Boolector
import qualified Data.SBV.Provers.CVC4       as CVC4
import qualified Data.SBV.Provers.Yices      as Yices
import qualified Data.SBV.Provers.Z3         as Z3
import qualified Data.SBV.Provers.MathSAT    as MathSAT
import qualified Data.SBV.Provers.ABC        as ABC

mkConfig :: SMTSolver -> SMTLibVersion -> [String] -> SMTConfig
mkConfig s smtVersion tweaks = SMTConfig { verbose        = False
                                         , timing         = False
                                         , sBranchTimeOut = Nothing
                                         , timeOut        = Nothing
                                         , printBase      = 10
                                         , printRealPrec  = 16
                                         , smtFile        = Nothing
                                         , solver         = s
                                         , solverTweaks   = tweaks
                                         , smtLibVersion  = smtVersion
                                         , satCmd         = "(check-sat)"
                                         , roundingMode   = RoundNearestTiesToEven
                                         , useLogic       = Nothing
                                         }

-- | Default configuration for the Boolector SMT solver
boolector :: SMTConfig
boolector = mkConfig Boolector.boolector SMTLib2 []

-- | Default configuration for the CVC4 SMT Solver.
cvc4 :: SMTConfig
cvc4 = mkConfig CVC4.cvc4 SMTLib2 []

-- | Default configuration for the Yices SMT Solver.
yices :: SMTConfig
yices = mkConfig Yices.yices SMTLib2 []

-- | Default configuration for the Z3 SMT solver
z3 :: SMTConfig
z3 = mkConfig Z3.z3 SMTLib2 ["(set-option :smt.mbqi true) ; use model based quantifier instantiation"]

-- | Default configuration for the MathSAT SMT solver
mathSAT :: SMTConfig
mathSAT = mkConfig MathSAT.mathSAT SMTLib2 []

-- | Default configuration for the ABC synthesis and verification tool.
abc :: SMTConfig
abc = mkConfig ABC.abc SMTLib2 []

-- | The default solver used by SBV. This is currently set to z3.
defaultSMTCfg :: SMTConfig
defaultSMTCfg = z3

-- | A predicate is a symbolic program that returns a (symbolic) boolean value. For all intents and
-- purposes, it can be treated as an n-ary function from symbolic-values to a boolean. The 'Symbolic'
-- monad captures the underlying representation, and can/should be ignored by the users of the library,
-- unless you are building further utilities on top of SBV itself. Instead, simply use the 'Predicate'
-- type when necessary.
type Predicate = Symbolic SBool

-- | A type @a@ is provable if we can turn it into a predicate.
-- Note that a predicate can be made from a curried function of arbitrary arity, where
-- each element is either a symbolic type or up-to a 7-tuple of symbolic-types. So
-- predicates can be constructed from almost arbitrary Haskell functions that have arbitrary
-- shapes. (See the instance declarations below.)
class Provable a where
  -- | Turns a value into a universally quantified predicate, internally naming the inputs.
  -- In this case the sbv library will use names of the form @s1, s2@, etc. to name these variables
  -- Example:
  --
  -- >  forAll_ $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- is a predicate with two arguments, captured using an ordinary Haskell function. Internally,
  -- @x@ will be named @s0@ and @y@ will be named @s1@.
  forAll_ :: a -> Predicate
  -- | Turns a value into a predicate, allowing users to provide names for the inputs.
  -- If the user does not provide enough number of names for the variables, the remaining ones
  -- will be internally generated. Note that the names are only used for printing models and has no
  -- other significance; in particular, we do not check that they are unique. Example:
  --
  -- >  forAll ["x", "y"] $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- This is the same as above, except the variables will be named @x@ and @y@ respectively,
  -- simplifying the counter-examples when they are printed.
  forAll  :: [String] -> a -> Predicate
  -- | Turns a value into an existentially quantified predicate. (Indeed, 'exists' would have been
  -- a better choice here for the name, but alas it's already taken.)
  forSome_ :: a -> Predicate
  -- | Version of 'forSome' that allows user defined names
  forSome :: [String] -> a -> Predicate

instance Provable Predicate where
  forAll_    = id
  forAll []  = id
  forAll xs  = error $ "SBV.forAll: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs
  forSome_   = id
  forSome [] = id
  forSome xs = error $ "SBV.forSome: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs

instance Provable SBool where
  forAll_   = return
  forAll _  = return
  forSome_  = return
  forSome _ = return

{-
-- The following works, but it lets us write properties that
-- are not useful.. Such as: prove $ \x y -> (x::SInt8) == y
-- Running that will throw an exception since Haskell's equality
-- is not be supported by symbolic things. (Needs .==).
instance Provable Bool where
  forAll_  x  = forAll_   (if x then true else false :: SBool)
  forAll s x  = forAll s  (if x then true else false :: SBool)
  forSome_  x = forSome_  (if x then true else false :: SBool)
  forSome s x = forSome s (if x then true else false :: SBool)
-}

-- Functions
instance (SymWord a, Provable p) => Provable (SBV a -> p) where
  forAll_        k = forall_   >>= \a -> forAll_   $ k a
  forAll (s:ss)  k = forall s  >>= \a -> forAll ss $ k a
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ k a
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ k a
  forSome []     k = forSome_ k

-- SFunArrays (memory, functional representation), only supported universally for the time being
instance (HasKind a, HasKind b, Provable p) => Provable (SArray a b -> p) where
  forAll_       k = declNewSArray (\t -> "array_" ++ show t) Nothing >>= \a -> forAll_   $ k a
  forAll (s:ss) k = declNewSArray (const s)                  Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k
  forSome_      _ = error "SBV.forSome: Existential arrays are not currently supported."
  forSome _     _ = error "SBV.forSome: Existential arrays are not currently supported."

-- SArrays (memory, SMT-Lib notion of arrays), only supported universally for the time being
instance (HasKind a, HasKind b, Provable p) => Provable (SFunArray a b -> p) where
  forAll_       k = declNewSFunArray Nothing >>= \a -> forAll_   $ k a
  forAll (_:ss) k = declNewSFunArray Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k
  forSome_      _ = error "SBV.forSome: Existential arrays are not currently supported."
  forSome _     _ = error "SBV.forSome: Existential arrays are not currently supported."

-- 2 Tuple
instance (SymWord a, SymWord b, Provable p) => Provable ((SBV a, SBV b) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b -> k (a, b)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b -> k (a, b)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b -> k (a, b)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b -> k (a, b)
  forSome []     k = forSome_ k

-- 3 Tuple
instance (SymWord a, SymWord b, SymWord c, Provable p) => Provable ((SBV a, SBV b, SBV c) -> p) where
  forAll_       k  = forall_  >>= \a -> forAll_   $ \b c -> k (a, b, c)
  forAll (s:ss) k  = forall s >>= \a -> forAll ss $ \b c -> k (a, b, c)
  forAll []     k  = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c -> k (a, b, c)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c -> k (a, b, c)
  forSome []     k = forSome_ k

-- 4 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d -> k (a, b, c, d)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d -> k (a, b, c, d)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d -> k (a, b, c, d)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d -> k (a, b, c, d)
  forSome []     k = forSome_ k

-- 5 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e -> k (a, b, c, d, e)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e -> k (a, b, c, d, e)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e -> k (a, b, c, d, e)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e -> k (a, b, c, d, e)
  forSome []     k = forSome_ k

-- 6 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f -> k (a, b, c, d, e, f)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f -> k (a, b, c, d, e, f)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f -> k (a, b, c, d, e, f)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f -> k (a, b, c, d, e, f)
  forSome []     k = forSome_ k

-- 7 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome []     k = forSome_ k

-- | Prove a predicate, equivalent to @'proveWith' 'defaultSMTCfg'@
prove :: Provable a => a -> IO ThmResult
prove = proveWith defaultSMTCfg

-- | Find a satisfying assignment for a predicate, equivalent to @'satWith' 'defaultSMTCfg'@
sat :: Provable a => a -> IO SatResult
sat = satWith defaultSMTCfg

-- | Check that all the 'sAssert' calls are safe, equivalent to @'safeWith' 'defaultSMTCfg'@
safe :: SExecutable a => a -> IO [SafeResult]
safe = safeWith defaultSMTCfg

-- | Return all satisfying assignments for a predicate, equivalent to @'allSatWith' 'defaultSMTCfg'@.
-- Satisfying assignments are constructed lazily, so they will be available as returned by the solver
-- and on demand.
--
-- NB. Uninterpreted constant/function values and counter-examples for array values are ignored for
-- the purposes of @'allSat'@. That is, only the satisfying assignments modulo uninterpreted functions and
-- array inputs will be returned. This is due to the limitation of not having a robust means of getting a
-- function counter-example back from the SMT solver.
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith defaultSMTCfg

-- | Check if the given constraints are satisfiable, equivalent to @'isVacuousWith' 'defaultSMTCfg'@.
-- See the function 'constrain' for an example use of 'isVacuous'.
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith defaultSMTCfg

-- Decision procedures (with optional timeout)

-- | Check whether a given property is a theorem, with an optional time out and the given solver.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isTheoremWith :: Provable a => SMTConfig -> Maybe Int -> a -> IO (Maybe Bool)
isTheoremWith cfg mbTo p = do r <- proveWith cfg{timeOut = mbTo} p
                              case r of
                                ThmResult (Unsatisfiable _) -> return $ Just True
                                ThmResult (Satisfiable _ _) -> return $ Just False
                                ThmResult (TimeOut _)       -> return Nothing
                                _                           -> error $ "SBV.isTheorem: Received:\n" ++ show r

-- | Check whether a given property is satisfiable, with an optional time out and the given solver.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isSatisfiableWith :: Provable a => SMTConfig -> Maybe Int -> a -> IO (Maybe Bool)
isSatisfiableWith cfg mbTo p = do r <- satWith cfg{timeOut = mbTo} p
                                  case r of
                                    SatResult (Satisfiable _ _) -> return $ Just True
                                    SatResult (Unsatisfiable _) -> return $ Just False
                                    SatResult (TimeOut _)       -> return Nothing
                                    _                           -> error $ "SBV.isSatisfiable: Received: " ++ show r

-- | Checks theoremhood within the given optional time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isTheorem = isTheoremWith defaultSMTCfg

-- | Checks satisfiability within the given optional time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isSatisfiable = isSatisfiableWith defaultSMTCfg

-- | Compiles to SMT-Lib and returns the resulting program as a string. Useful for saving
-- the result to a file for off-line analysis, for instance if you have an SMT solver that's not natively
-- supported out-of-the box by the SBV library. It takes two arguments:
--
--    * version: The SMTLib-version to produce. Note that we currently only support SMTLib2.
--
--    * isSat  : If 'True', will translate it as a SAT query, i.e., in the positive. If 'False', will
--               translate as a PROVE query, i.e., it will negate the result. (In this case, the check-sat
--               call to the SMT solver will produce UNSAT if the input is a theorem, as usual.)
compileToSMTLib :: Provable a => SMTLibVersion   -- ^ Version of SMTLib to compile to. (Only SMTLib2 supported currently.)
                              -> Bool            -- ^ If True, translate directly, otherwise negate the goal. (Use True for SAT queries, False for PROVE queries.)
                              -> a
                              -> IO String
compileToSMTLib version isSat a = do
        t <- getClockTime
        let comments = ["Created on " ++ show t]
            cvt = case version of
                    SMTLib2 -> toSMTLib2
        (_, _, _, _, smtLibPgm) <- simulate cvt defaultSMTCfg isSat comments a
        let out = show smtLibPgm
        return $ out ++ "\n(check-sat)\n"

-- | Create SMT-Lib benchmarks, for supported versions of SMTLib. The first argument is the basename of the file.
-- The 'Bool' argument controls whether this is a SAT instance, i.e., translate the query
-- directly, or a PROVE instance, i.e., translate the negated query. (See the second boolean argument to
-- 'compileToSMTLib' for details.)
generateSMTBenchmarks :: Provable a => Bool -> FilePath -> a -> IO ()
generateSMTBenchmarks isSat f a = mapM_ gen [minBound .. maxBound]
  where gen v = do s <- compileToSMTLib v isSat a
                   let fn = f `addExtension` smtLibVersionExtension v
                   writeFile fn s
                   putStrLn $ "Generated " ++ show v ++ " benchmark " ++ show fn ++ "."

-- | Proves the predicate using the given SMT-solver
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith config a = simulate cvt config False [] a >>= callSolver False "Checking Theoremhood.." ThmResult config
  where cvt = case smtLibVersion config of
                SMTLib2 -> toSMTLib2

-- | Find a satisfying assignment using the given SMT-solver
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith config a = simulate cvt config True [] a >>= callSolver True "Checking Satisfiability.." SatResult config
  where cvt = case smtLibVersion config of
                SMTLib2 -> toSMTLib2

-- | Check if any of the assertions can be violated
safeWith :: SExecutable a => SMTConfig -> a -> IO [SafeResult]
safeWith cfg a = do
        res@Result{resAssertions=asserts} <- runSymbolic (True, cfg) $ sName_ a >>= output
        mapM (verify res) asserts
  where locInfo (Just ps) = Just $ let loc (f, sl) = concat [srcLocFile sl, ":", show (srcLocStartLine sl), ":", show (srcLocStartCol sl), ":", f]
                                   in intercalate ",\n " (map loc ps)
        locInfo _         = Nothing
        verify res (msg, cs, cond) = do SatResult result <- runProofOn cvt cfg True [] pgm >>= callSolver True msg SatResult cfg
                                        return $ SafeResult (locInfo (getCallStack `fmap` cs), msg, result)
           where pgm = res { resInputs  = [(EX, n) | (_, n) <- resInputs res]   -- make everything existential
                           , resOutputs = [cond]
                           }
                 cvt = case smtLibVersion cfg of
                         SMTLib2 -> toSMTLib2

-- | Check if a safe-call was safe or not, turning a 'SafeResult' to a Bool.
isSafe :: SafeResult -> Bool
isSafe (SafeResult (_, _, result)) = case result of
                                       Unsatisfiable{} -> True
                                       Satisfiable{}   -> False
                                       Unknown{}       -> False   -- conservative
                                       ProofError{}    -> False   -- conservative
                                       TimeOut{}       -> False   -- conservative

-- | Determine if the constraints are vacuous using the given SMT-solver
isVacuousWith :: Provable a => SMTConfig -> a -> IO Bool
isVacuousWith config a = do
        Result ki tr uic is cs ts as uis ax asgn cstr asserts _ <- runSymbolic (True, config) $ forAll_ a >>= output
        case cstr of
           [] -> return False -- no constraints, no need to check
           _  -> do let is'  = [(EX, i) | (_, i) <- is] -- map all quantifiers to "exists" for the constraint check
                        res' = Result ki tr uic is' cs ts as uis ax asgn cstr asserts [trueSW]
                        cvt  = case smtLibVersion config of
                                 SMTLib2 -> toSMTLib2
                    SatResult result <- runProofOn cvt config True [] res' >>= callSolver True "Checking Satisfiability.." SatResult config
                    case result of
                      Unsatisfiable{} -> return True  -- constraints are unsatisfiable!
                      Satisfiable{}   -> return False -- constraints are satisfiable!
                      Unknown{}       -> error "SBV: isVacuous: Solver returned unknown!"
                      ProofError _ ls -> error $ "SBV: isVacuous: error encountered:\n" ++ unlines ls
                      TimeOut _       -> error "SBV: isVacuous: time-out."

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith config p = do
        let converter  = case smtLibVersion config of
                           SMTLib2 -> toSMTLib2
        msg "Checking Satisfiability, all solutions.."
        sbvPgm@(qinps, _, ki, _, _) <- simulate converter config True [] p
        let usorts = [s | us@(KUserSort s _) <- Set.toList ki, isFree us]
                where isFree (KUserSort _ (Left _, _)) = True
                      isFree _                         = False
        unless (null usorts) $ msg $  "SBV.allSat: Uninterpreted sorts present: " ++ unwords usorts
                                   ++ "\n               SBV will use equivalence classes to generate all-satisfying instances."
        results <- unsafeInterleaveIO $ go sbvPgm (1::Int) []
        -- See if there are any existentials below any universals
        -- If such is the case, then the solutions are unique upto prefix existentials
        let w = ALL `elem` map fst qinps
        return $ AllSatResult (w,  results)
  where msg = when (verbose config) . putStrLn . ("** " ++)
        go sbvPgm = loop
          where loop !n nonEqConsts = do
                  curResult <- invoke nonEqConsts n sbvPgm
                  case curResult of
                    Nothing            -> return []
                    Just (SatResult r) -> let cont model = do rest <- unsafeInterleaveIO $ loop (n+1) (modelAssocs model : nonEqConsts)
                                                              return (r : rest)
                                          in case r of
                                               Satisfiable   _ (SMTModel []) -> return [r]
                                               Unknown       _ (SMTModel []) -> return [r]
                                               ProofError    _ _             -> return [r]
                                               TimeOut       _               -> return []
                                               Unsatisfiable _               -> return []
                                               Satisfiable   _ model         -> cont model
                                               Unknown       _ model         -> cont model
        invoke nonEqConsts n (qinps, skolemMap, _, _, smtLibPgm) = do
               msg $ "Looking for solution " ++ show n
               case addNonEqConstraints (roundingMode config) qinps nonEqConsts smtLibPgm of
                 Nothing ->  -- no new constraints added, stop
                            return Nothing
                 Just finalPgm -> do msg $ "Generated SMTLib program:\n" ++ finalPgm
                                     smtAnswer <- engine (solver config) (updateName (n-1) config) True qinps skolemMap finalPgm
                                     msg "Done.."
                                     return $ Just $ SatResult smtAnswer
        updateName i cfg = cfg{smtFile = upd `fmap` smtFile cfg}
               where upd nm = let (b, e) = splitExtension nm in b ++ "_allSat_" ++ show i ++ e

type SMTProblem = ( [(Quantifier, NamedSymVar)]      -- inputs
                  , [Either SW (SW, [SW])]           -- skolem-map
                  , Set.Set Kind                     -- kinds used
                  , [(String, Maybe CallStack, SW)]  -- assertions
                  , SMTLibPgm                        -- SMTLib representation
                  )

callSolver :: Bool -> String -> (SMTResult -> b) -> SMTConfig -> SMTProblem -> IO b
callSolver isSat checkMsg wrap config (qinps, skolemMap, _, _, smtLibPgm) = do
       let msg = when (verbose config) . putStrLn . ("** " ++)
       msg checkMsg
       let finalPgm = intercalate "\n" (pre ++ post) where SMTLibPgm _ (_, pre, post) = smtLibPgm
       msg $ "Generated SMTLib program:\n" ++ finalPgm
       smtAnswer <- engine (solver config) config isSat qinps skolemMap finalPgm
       msg "Done.."
       return $ wrap smtAnswer

simulate :: Provable a => SMTLibConverter -> SMTConfig -> Bool -> [String] -> a -> IO SMTProblem
simulate converter config isSat comments predicate = do
        let msg = when (verbose config) . putStrLn . ("** " ++)
            isTiming = timing config
        msg "Starting symbolic simulation.."
        res <- timeIf isTiming "problem construction" $ runSymbolic (isSat, config) $ (if isSat then forSome_ else forAll_) predicate >>= output
        msg $ "Generated symbolic trace:\n" ++ show res
        msg "Translating to SMT-Lib.."
        runProofOn converter config isSat comments res

runProofOn :: SMTLibConverter -> SMTConfig -> Bool -> [String] -> Result -> IO SMTProblem
runProofOn converter config isSat comments res =
        let isTiming   = timing config
            solverCaps = capabilities (solver config)
        in case res of
             Result ki _qcInfo _codeSegs is consts tbls arrs uis axs pgm cstrs assertions [o@(SW KBool _)] ->
               timeIf isTiming "translation"
                $ let skolemMap = skolemize (if isSat then is else map flipQ is)
                           where flipQ (ALL, x) = (EX, x)
                                 flipQ (EX, x)  = (ALL, x)
                                 skolemize :: [(Quantifier, NamedSymVar)] -> [Either SW (SW, [SW])]
                                 skolemize qinps = go qinps ([], [])
                                   where go []                   (_,  sofar) = reverse sofar
                                         go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                                         go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)
                  in return (is, skolemMap, ki, assertions, converter (roundingMode config) (useLogic config) solverCaps ki isSat comments is skolemMap consts tbls arrs uis axs pgm cstrs o)
             Result{resOutputs = os} -> case length os of
                           0  -> error $ "Impossible happened, unexpected non-outputting result\n" ++ show res
                           1  -> error $ "Impossible happened, non-boolean output in " ++ show os
                                       ++ "\nDetected while generating the trace:\n" ++ show res
                           _  -> error $ "User error: Multiple output values detected: " ++ show os
                                       ++ "\nDetected while generating the trace:\n" ++ show res
                                       ++ "\n*** Check calls to \"output\", they are typically not needed!"

-- | Run an external proof on the given condition to see if it is satisfiable.
internalSATCheck :: SMTConfig -> SBool -> State -> String -> IO SatResult
internalSATCheck cfg condInPath st msg = do
   sw <- sbvToSW st condInPath
   () <- forceSWArg sw
   Result ki tr uic is cs ts as uis ax asgn cstr assertions _ <- extractSymbolicSimulationState st
   let -- Construct the corresponding sat-checker for the branch. Note that we need to
       -- forget about the quantifiers and just use an "exist", as we're looking for a
       -- point-satisfiability check here; whatever the original program was.
       pgm = Result ki tr uic [(EX, n) | (_, n) <- is] cs ts as uis ax asgn cstr assertions [sw]
       cvt = case smtLibVersion cfg of
                SMTLib2 -> toSMTLib2
   runProofOn cvt cfg True [] pgm >>= callSolver True msg SatResult cfg
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
