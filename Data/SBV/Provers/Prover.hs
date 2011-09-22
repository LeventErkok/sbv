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
       , yices, z3
       , compileToSMTLib
       ) where

import qualified Control.Exception as E

import Control.Concurrent             (forkIO)
import Control.Concurrent.Chan.Strict (newChan, writeChan, getChanContents)
import Control.Monad                  (when)
import Data.List                      (intercalate)
import Data.Maybe                     (fromJust, isJust, catMaybes)
import System.Time                    (getClockTime)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import qualified Data.SBV.Provers.Yices as Yices
import qualified Data.SBV.Provers.Z3    as Z3
import Data.SBV.Utils.TDiff

-- | Default configuration for the Yices SMT Solver.
yices :: SMTConfig
yices = SMTConfig {verbose = False, timing = False, timeOut = Nothing, printBase = 10, smtFile = Nothing, solver = Yices.yices, useSMTLib2 = False}

-- | Default configuration for the Z3 SMT solver
z3 :: SMTConfig
z3 = yices { solver = Z3.z3, useSMTLib2 = True }

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
  -- If the user does not provide enough number of names for the variables, the remaining ones
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
  forAll_  = return
  forAll _ = return

{-
-- The following works, but it lets us write properties that
-- are not useful.. Such as: prove $ \x y -> (x::SInt8) == y
-- Running that will throw an exception since Haskell's equality
-- is not be supported by symbolic things. (Needs .==).
instance Provable Bool where
  forAll_  x = forAll_  (if x then true else false :: SBool)
  forAll s x = forAll s (if x then true else false :: SBool)
-}

-- Functions
instance (SymWord a, Provable p) => Provable (SBV a -> p) where
  forAll_       k = forall_  >>= \a -> forAll_   $ k a
  forAll (s:ss) k = forall s >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k

-- Arrays (memory)
instance (HasSignAndSize a, HasSignAndSize b, SymArray array, Provable p) => Provable (array a b -> p) where
  forAll_       k = newArray_  Nothing >>= \a -> forAll_   $ k a
  forAll (s:ss) k = newArray s Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k

-- 2 Tuple
instance (SymWord a, SymWord b, Provable p) => Provable ((SBV a, SBV b) -> p) where
  forAll_       k = forall_  >>= \a -> forAll_   $ \b -> k (a, b)
  forAll (s:ss) k = forall s >>= \a -> forAll ss $ \b -> k (a, b)
  forAll []     k = forAll_ k

-- 3 Tuple
instance (SymWord a, SymWord b, SymWord c, Provable p) => Provable ((SBV a, SBV b, SBV c) -> p) where
  forAll_       k = forall_  >>= \a -> forAll_   $ \b c -> k (a, b, c)
  forAll (s:ss) k = forall s >>= \a -> forAll ss $ \b c -> k (a, b, c)
  forAll []     k = forAll_ k

-- 4 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  forAll_       k = forall_  >>= \a -> forAll_   $ \b c d -> k (a, b, c, d)
  forAll (s:ss) k = forall s >>= \a -> forAll ss $ \b c d -> k (a, b, c, d)
  forAll []     k = forAll_ k

-- 5 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  forAll_       k = forall_  >>= \a -> forAll_   $ \b c d e -> k (a, b, c, d, e)
  forAll (s:ss) k = forall s >>= \a -> forAll ss $ \b c d e -> k (a, b, c, d, e)
  forAll []     k = forAll_ k

-- 6 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  forAll_       k = forall_  >>= \a -> forAll_   $ \b c d e f -> k (a, b, c, d, e, f)
  forAll (s:ss) k = forall s >>= \a -> forAll ss $ \b c d e f -> k (a, b, c, d, e, f)
  forAll []     k = forAll_ k

-- 7 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  forAll_       k = forall_  >>= \a -> forAll_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll (s:ss) k = forall s >>= \a -> forAll ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll []     k = forAll_ k

-- | Prove a predicate, equivalent to @'proveWith' 'yices'@
prove :: Provable a => a -> IO ThmResult
prove = proveWith yices

-- | Find a satisfying assignment for a predicate, equivalent to @'satWith' 'yices'@
sat :: Provable a => a -> IO SatResult
sat = satWith yices

-- | Return all satisfying assignments for a predicate, equivalent to @'allSatWith' 'yices'@.
-- Satisfying assignments are constructed lazily, so they will be available as returned by the solver
-- and on demand.
--
-- NB. Uninterpreted constant/function values and counter-examples for array values are ignored for
-- the purposes of @'allSat'@. That is, only the satisfying assignments modulo uninterpreted functions and
-- array inputs will be returned. This is due to the limitation of not having a robust means of getting a
-- function counter-example back from the SMT solver.
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith yices

-- Decision procedures (with optional timeout)
checkTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
checkTheorem mbTo p = do r <- pr p
                         case r of
                           ThmResult (Unsatisfiable _) -> return $ Just True
                           ThmResult (Satisfiable _ _) -> return $ Just False
                           ThmResult (TimeOut _)       -> return Nothing
                           _                           -> error $ "SBV.isTheorem: Received:\n" ++ show r
   where pr = maybe prove (\i -> proveWith (yices{timeOut = Just i})) mbTo

checkSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
checkSatisfiable mbTo p = do r <- s p
                             case r of
                               SatResult (Satisfiable _ _) -> return $ Just True
                               SatResult (Unsatisfiable _) -> return $ Just False
                               SatResult (TimeOut _)       -> return Nothing
                               _                           -> error $ "SBV.isSatisfiable: Received: " ++ show r
   where s = maybe sat (\i -> satWith yices{timeOut = Just i}) mbTo

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
numberOfModels p = do AllSatResult (_, rs) <- allSat p
                      return $ length rs

-- | Compiles to SMT-Lib and returns the resulting program as a string. Useful for saving
-- the result to a file for off-line analysis, for instance if you have an SMT solver that's not natively
-- supported out-of-the box by the SBV library. If 'smtLib2' parameter is False, then we will generate
-- SMTLib1 output, otherwise we will generate SMTLib2 output
compileToSMTLib :: Provable a => Bool -> a -> IO String
compileToSMTLib smtLib2 a = do
        t <- getClockTime
        let comments = ["Created on " ++ show t]
            cvt = if smtLib2 then toSMTLib2 else toSMTLib1
        (_, _, _, smtLibPgm) <- simulate cvt yices False comments a
        return $ show smtLibPgm ++ "\n"

-- | Proves the predicate using the given SMT-solver
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith config a = simulate cvt config False [] a >>= callSolver False "Checking Theoremhood.." ThmResult config
  where cvt = if useSMTLib2 config then toSMTLib2 else toSMTLib1

-- | Find a satisfying assignment using the given SMT-solver
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith config a = simulate cvt config True [] a >>= callSolver True "Checking Satisfiability.." SatResult config
  where cvt = if useSMTLib2 config then toSMTLib2 else toSMTLib1

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith config p = do
        let converter = if useSMTLib2 config then toSMTLib2 else toSMTLib1
        msg "Checking Satisfiability, all solutions.."
        sbvPgm@(qinps, _, _, _) <- simulate converter config True [] p
        resChan <- newChan
        let add  = writeChan resChan . Just
            stop = writeChan resChan Nothing
            final r = add r >> stop
            die m  = final (ProofError config [m])
            -- only fork if non-verbose.. otherwise stdout gets garbled
            fork io = if verbose config then io else forkIO io >> return ()
        fork $ E.catch (go sbvPgm add stop final (1::Int) [])
                       (\e -> die (show (e::E.SomeException)))
        results <- getChanContents resChan
        -- See if there are any existentials below any universals
        -- If such is the case, then the solutions are unique upto prefix existentials
        let w = ALL `elem` map fst qinps
        return $ AllSatResult (w,  map fromJust (takeWhile isJust results))
  where msg = when (verbose config) . putStrLn . ("** " ++)
        go sbvPgm add stop final = loop
          where loop !n nonEqConsts = do
                  curResult <- invoke nonEqConsts n sbvPgm
                  case curResult of
                    Nothing     -> stop
                    Just (SatResult r) -> case r of
                                            Satisfiable _ (SMTModel [] _ _) -> final r
                                            Unknown _ (SMTModel [] _ _)     -> final r
                                            ProofError _ _                  -> final r
                                            TimeOut _                       -> stop
                                            Unsatisfiable _                 -> stop
                                            Satisfiable _ model             -> add r >> loop (n+1) (modelAssocs model : nonEqConsts)
                                            Unknown     _ model             -> add r >> loop (n+1) (modelAssocs model : nonEqConsts)
        invoke nonEqConsts n (qinps, modelMap, skolemMap, smtLibPgm) = do
               msg $ "Looking for solution " ++ show n
               case addNonEqConstraints qinps nonEqConsts smtLibPgm of
                 Nothing ->  -- no new constraints added, stop
                            return Nothing
                 Just finalPgm -> do msg $ "Generated SMTLib program:\n" ++ finalPgm
                                     smtAnswer <- engine (solver config) config True qinps modelMap skolemMap finalPgm
                                     msg "Done.."
                                     return $ Just $ SatResult smtAnswer

callSolver :: Bool -> String -> (SMTResult -> b) -> SMTConfig -> ([(Quantifier, NamedSymVar)], [(String, UnintKind)], [Either SW (SW, [SW])], SMTLibPgm) -> IO b
callSolver isSat checkMsg wrap config (qinps, modelMap, skolemMap, smtLibPgm) = do
       let msg = when (verbose config) . putStrLn . ("** " ++)
       msg checkMsg
       let finalPgm = intercalate "\n" (pre ++ post) where SMTLibPgm _ (_, pre, post) = smtLibPgm
       msg $ "Generated SMTLib program:\n" ++ finalPgm
       smtAnswer <- engine (solver config) config isSat qinps modelMap skolemMap finalPgm
       msg "Done.."
       return $ wrap smtAnswer

simulate :: Provable a => SMTLibConverter -> SMTConfig -> Bool -> [String] -> a -> IO ([(Quantifier, NamedSymVar)], [(String, UnintKind)], [Either SW (SW, [SW])], SMTLibPgm)
simulate converter config isSat comments predicate = do
        let msg = when (verbose config) . putStrLn . ("** " ++)
            isTiming = timing config
        msg "Starting symbolic simulation.."
        res <- timeIf isTiming "problem construction" $ runSymbolic $ forAll_ predicate >>= output
        msg $ "Generated symbolic trace:\n" ++ show res
        msg "Translating to SMT-Lib.."
        case res of
          Result is consts tbls arrs uis axs pgm [o@(SW (False, 1) _)] | sizeOf o == 1 ->
             timeIf isTiming "translation" $ do let uiMap     = catMaybes (map arrayUIKind arrs) ++ map unintFnUIKind uis
                                                    skolemMap = skolemize (if isSat then is else map flipQ is)
                                                        where flipQ (ALL, x) = (EX, x)
                                                              flipQ (EX, x)  = (ALL, x)
                                                              skolemize :: [(Quantifier, NamedSymVar)] -> [Either SW (SW, [SW])]
                                                              skolemize qinps = go qinps ([], [])
                                                                where go []                   (_,  sofar) = reverse sofar
                                                                      go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                                                                      go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)
                                                return (is, uiMap, skolemMap, converter isSat comments is skolemMap consts tbls arrs uis axs pgm o)
          Result _is _consts _tbls _arrs _uis _axs _pgm os -> case length os of
                        0  -> error $ "Impossible happened, unexpected non-outputting result\n" ++ show res
                        1  -> error $ "Impossible happened, non-boolean output in " ++ show os
                                    ++ "\nDetected while generating the trace:\n" ++ show res
                        _  -> error $ "User error: Multiple output values detected: " ++ show os
                                    ++ "\nDetected while generating the trace:\n" ++ show res
                                    ++ "\n*** Check calls to \"output\", they are typically not needed!"

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
