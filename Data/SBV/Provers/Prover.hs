-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Prover
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Provable abstraction and the connection to SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate, Provable(..)
       , ThmResult(..), SatResult(..), AllSatResult(..), SMTResult(..)
       , isSatisfiable, isTheorem
       , isSatisfiableWithin, isTheoremWithin
       , numberOfModels
       , Equality(..)
       , prove, proveWith
       , sat, satWith
       , allSat, allSatWith
       , SatModel(..), getModel, displayModels
       , defaultSMTCfg, verboseSMTCfg, timingSMTCfg, verboseTimingSMTCfg
       , Yices.yices
       , timeout
       ) where


import Control.Monad                  (when)
import Control.Concurrent             (forkIO)
import Control.Concurrent.Chan.Strict (newChan, writeChan, getChanContents)
import Data.Maybe                     (fromJust, isJust)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import qualified Data.SBV.Provers.Yices as Yices
import Data.SBV.Utils.TDiff

-- | Default configuration for the SMT solver. Non-verbose, non-timing, prints results in base 10, and uses
-- the Yices SMT solver.
defaultSMTCfg :: SMTConfig
defaultSMTCfg = SMTConfig {verbose = False, timing  = False, printBase = 10, solver = Yices.yices}

-- | Same as 'defaultSMTCfg', except verbose
verboseSMTCfg :: SMTConfig
verboseSMTCfg = defaultSMTCfg {verbose=True}

-- | Same as 'defaultSMTCfg', except prints timing info
timingSMTCfg :: SMTConfig
timingSMTCfg  = defaultSMTCfg {timing=True}

-- | Same as 'defaultSMTCfg', except both verbose and timing info
verboseTimingSMTCfg :: SMTConfig
verboseTimingSMTCfg = timingSMTCfg {verbose=True}

-- We might need a better system if we add more backend solvers
-- | Adds a time out of @n@ seconds to a given solver configuration
timeout :: Int -> SMTConfig -> SMTConfig
timeout n s
 | nm == name Yices.yices = s{solver = Yices.timeout n (solver s)}
 | True                   = error $ "SBV.Prover.timeout: Solver " ++ show nm ++ " does not support time-outs"
 where nm = name (solver s)

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
  -- | Turns a value into a predicate, internally naming the inputs.
  -- In this case the sbv library will use names of the form @s1, s2@, etc. to name these variables
  -- Example:
  --
  -- >  forAll_ $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- is a predicate with two arguments, captured using an ordinary Haskell function. Internally,
  -- @x@ will be named @s0@ and @y@ will be named @s1@.
  forAll_ :: a -> Predicate
  -- | Turns a value into a predicate, allowing users to provide names for the inputs.
  -- If the user does not provide enough number of names for the free variables, the remaining ones
  -- will be internally generated. Note that the names are only used for printing models and has no
  -- other significance; in particular, we do not check that they are unique. Example:
  --
  -- >  forAll ["x", "y"] $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- This is the same as above, except the variables will be named @x@ and @y@ respectively,
  -- simplifying the counter-examples when they are printed.
  forAll  :: [String] -> a -> Predicate

instance Provable Predicate where
  forAll_  = id
  forAll _ = id

instance Provable SBool where
  forAll_  = output
  forAll _ = output

{-
-- The following works, but it lets us write properties that
-- are typically bogus.. Such as: prove $ \x y -> (x::SInt8) == y
instance Provable Bool where
  forAll_  x = forAll_  (if x then true else false :: SBool)
  forAll s x = forAll s (if x then true else false :: SBool)
-}

-- Functions
instance (SymWord a, Provable p) => Provable (SBV a -> p) where
  forAll_       k = free_  >>= \a -> forAll_   $ k a
  forAll (s:ss) k = free s >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k

-- Memory
instance (HasSignAndSize a, HasSignAndSize b, SymArray array, Provable p) => Provable (array a b -> p) where
  forAll_       k = newArray_  Nothing >>= \a -> forAll_   $ k a
  forAll (s:ss) k = newArray s Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k

-- 2 Tuple
instance (SymWord a, SymWord b, Provable p) => Provable ((SBV a, SBV b) -> p) where
  forAll_       k = free_  >>= \a -> forAll_   $ \b -> k (a, b)
  forAll (s:ss) k = free s >>= \a -> forAll ss $ \b -> k (a, b)
  forAll []     k = forAll_ k

-- 3 Tuple
instance (SymWord a, SymWord b, SymWord c, Provable p) => Provable ((SBV a, SBV b, SBV c) -> p) where
  forAll_       k = free_  >>= \a -> forAll_   $ \b c -> k (a, b, c)
  forAll (s:ss) k = free s >>= \a -> forAll ss $ \b c -> k (a, b, c)
  forAll []     k = forAll_ k

-- 4 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  forAll_       k = free_  >>= \a -> forAll_   $ \b c d -> k (a, b, c, d)
  forAll (s:ss) k = free s >>= \a -> forAll ss $ \b c d -> k (a, b, c, d)
  forAll []     k = forAll_ k

-- 5 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  forAll_       k = free_  >>= \a -> forAll_   $ \b c d e -> k (a, b, c, d, e)
  forAll (s:ss) k = free s >>= \a -> forAll ss $ \b c d e -> k (a, b, c, d, e)
  forAll []     k = forAll_ k

-- 6 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  forAll_       k = free_  >>= \a -> forAll_   $ \b c d e f -> k (a, b, c, d, e, f)
  forAll (s:ss) k = free s >>= \a -> forAll ss $ \b c d e f -> k (a, b, c, d, e, f)
  forAll []     k = forAll_ k

-- 7 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  forAll_       k = free_  >>= \a -> forAll_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll (s:ss) k = free s >>= \a -> forAll ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll []     k = forAll_ k

-- | Prove a predicate, equivalent to @'proveWith' 'defaultSMTCfg'@
prove :: Provable a => a -> IO ThmResult
prove = proveWith defaultSMTCfg

-- | Find a satisfying assignment for a predicate, equivalent to @'satWith' 'defaultSMTCfg'@
sat :: Provable a => a -> IO SatResult
sat = satWith defaultSMTCfg

-- | Return all satisfying assignments for a predicate, equivalent to @'allSatWith' 'defaultSMTCfg'@.
-- Satisfying assignments are constructed lazily, so they will be available as returned by the solver
-- and on demand.
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith defaultSMTCfg

-- Decision procedures (with optional timeout)
checkTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
checkTheorem mbTo p = do r <- pr p
                         case r of
                           ThmResult (Unsatisfiable _) -> return $ Just True
                           ThmResult (Satisfiable _ _) -> return $ Just False
                           ThmResult (TimeOut _)       -> return Nothing
                           _                           -> error $ "SBV.isTheorem: Received:\n" ++ show r
   where pr = maybe prove (\i -> proveWith (timeout i defaultSMTCfg)) mbTo

checkSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
checkSatisfiable mbTo p = do r <- s p
                             case r of
                               SatResult (Satisfiable _ _) -> return $ Just True
                               SatResult (Unsatisfiable _) -> return $ Just False
                               SatResult (TimeOut _)       -> return Nothing
                               _                           -> error $ "SBV.isSatisfiable: Received: " ++ show r
   where s = maybe sat (\i -> satWith (timeout i defaultSMTCfg)) mbTo

-- | Checks theoremhood within the given time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isTheoremWithin :: Provable a => Int -> a -> IO (Maybe Bool)
isTheoremWithin i = checkTheorem (Just i)

-- | Checks satisfiability within the given time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isSatisfiableWithin :: Provable a => Int -> a -> IO (Maybe Bool)
isSatisfiableWithin i = checkSatisfiable (Just i)

-- | Checks theoremhood
isTheorem :: Provable a => a -> IO Bool
isTheorem p = fromJust `fmap` checkTheorem Nothing p

-- | Checks satisfiability
isSatisfiable :: Provable a => a -> IO Bool
isSatisfiable p = fromJust `fmap` checkSatisfiable Nothing p

-- | Returns the number of models that satisfy the predicate, as it would
-- be returned by 'allSat'. Note that the number of models is always a
-- finite number, and hence this will always return a result. Of course,
-- computing it might take quite long, as it literally generates and counts
-- the number of satisfying models.
numberOfModels :: Provable a => a -> IO Int
numberOfModels p = do AllSatResult rs <- allSat p
                      return $ sum $ map walk rs
  where walk (Satisfiable{}) = 1
        -- shouldn't happen, but just in case
        walk r               = error $ "numberOfModels: Unexpected result from an allSat check: " ++ show (AllSatResult [r])

-- | Proves the predicate using the given SMT-solver
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith config a = generateTrace config False a >>= callSolver [] "Checking Theoremhood.." ThmResult config

-- | Find a satisfying assignment using the given SMT-solver
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith config a = generateTrace config True a >>= callSolver [] "Checking Satisfiability.." SatResult config

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith config p = do when (verbose config) $ putStrLn  "** Checking Satisfiability, all solutions.."
                         sbvPgm <- generateTrace config True p
                         resChan <- newChan
                         let add  = writeChan resChan . Just
                             stop = writeChan resChan Nothing
                             final r = add r >> stop
                             -- only fork if non-verbose.. otherwise stdout gets garbled
                             fork io = if verbose config then io else forkIO io >> return ()
                         fork $ go sbvPgm add stop final (1::Int) []
                         results <- getChanContents resChan
                         return $ AllSatResult $ map fromJust $ takeWhile isJust results
  where go sbvPgm add stop final = loop
          where loop !n nonEqConsts = do
                  SatResult r <- callSolver nonEqConsts ("Looking for solution " ++ show n) SatResult config sbvPgm
                  case r of
                    Satisfiable _ (SMTModel [] _) -> final r
                    Unknown _ (SMTModel [] _)     -> final r
                    ProofError _ _                -> final r
                    TimeOut _                     -> stop
                    Unsatisfiable _               -> stop
                    Satisfiable _ model           -> add r >> loop (n+1) (modelAssocs model : nonEqConsts)
                    Unknown     _ model           -> add r >> loop (n+1) (modelAssocs model : nonEqConsts)

callSolver :: [[(String, CW)]] -> String -> (SMTResult -> b) -> SMTConfig -> ([NamedSymVar], SMTLibPgm) -> IO b
callSolver nonEqConstraints checkMsg wrap config (inps, smtLibPgm) = do
        let msg = when (verbose config) . putStrLn . ("** " ++)
        msg checkMsg
        let finalPgm = addNonEqConstraints nonEqConstraints smtLibPgm
        msg $ "Generated SMTLib program:\n" ++ finalPgm
        smtAnswer <- engine (solver config) config inps finalPgm
        msg "Done.."
        return $ wrap smtAnswer

generateTrace :: Provable a => SMTConfig -> Bool -> a -> IO ([NamedSymVar], SMTLibPgm)
generateTrace config isSat predicate = do
        let msg = when (verbose config) . putStrLn . ("** " ++)
            isTiming = timing config
        msg "Generating a symbolic trace.."
        res <- timeIf isTiming "problem construction" $ runSymbolic $ forAll_ predicate
        msg $ "Generated symbolic trace:\n" ++ show res
        msg "Translating to SMT-Lib.."
        case res of
          Result is consts tbls arrs uis pgm [o@(SW{})] -> timeIf isTiming "translation" $ return (is, toSMTLib isSat is consts tbls arrs uis pgm o)
          _                                             -> error $ "SBVProver.callSolver: Impossible happened: " ++ show res

-- | Equality as a proof method. Allows for
-- very concise construction of equivalence proofs, which is very typical in
-- bit-precise proofs.
infix 4 ===
class Equality a where
  (===) :: a -> a -> IO ThmResult

instance (SymWord a, EqSymbolic z) => Equality (SBV a -> z) where
  k === l = prove $ \a -> k a .== l a

instance (SymWord a, SymWord b, EqSymbolic z) => Equality (SBV a -> SBV b -> z) where
  k === l = prove $ \a b -> k a b .== l a b

instance (SymWord a, SymWord b, EqSymbolic z) => Equality ((SBV a, SBV b) -> z) where
  k === l = prove $ \a b -> k (a, b) .== l (a, b)

instance (SymWord a, SymWord b, SymWord c, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> z) where
  k === l = prove $ \a b c -> k a b c .== l a b c

instance (SymWord a, SymWord b, SymWord c, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c) -> z) where
  k === l = prove $ \a b c -> k (a, b, c) .== l (a, b, c)

instance (SymWord a, SymWord b, SymWord c, SymWord d, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> z) where
  k === l = prove $ \a b c d -> k a b c d .== l a b c d

instance (SymWord a, SymWord b, SymWord c, SymWord d, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d) -> z) where
  k === l = prove $ \a b c d -> k (a, b, c, d) .== l (a, b, c, d)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> z) where
  k === l = prove $ \a b c d e -> k a b c d e .== l a b c d e

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e) -> z) where
  k === l = prove $ \a b c d e -> k (a, b, c, d, e) .== l (a, b, c, d, e)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> z) where
  k === l = prove $ \a b c d e f -> k a b c d e f .== l a b c d e f

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> z) where
  k === l = prove $ \a b c d e f -> k (a, b, c, d, e, f) .== l (a, b, c, d, e, f)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV g -> z) where
  k === l = prove $ \a b c d e f g -> k a b c d e f g .== l a b c d e f g

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> z) where
  k === l = prove $ \a b c d e f g -> k (a, b, c, d, e, f, g) .== l (a, b, c, d, e, f, g)
