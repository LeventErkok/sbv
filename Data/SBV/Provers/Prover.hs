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
       , isVacuous, isVacuousWith
       , SatModel(..), Modelable(..), displayModels
       , yices, z3, defaultSMTCfg
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

-- | The default solver used by SBV. This is currently set to yices.
defaultSMTCfg :: SMTConfig
defaultSMTCfg = yices

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

-- Arrays (memory), only supported universally for the time being
instance (HasSignAndSize a, HasSignAndSize b, SymArray array, Provable p) => Provable (array a b -> p) where
  forAll_       k = newArray_  Nothing >>= \a -> forAll_   $ k a
  forAll (s:ss) k = newArray s Nothing >>= \a -> forAll ss $ k a
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

-- | Check if the given constraints are satisfiable, equivalent to @'isVacuousWith' 'defaultSMTCfg'@. This
-- call can be used to ensure that the specified constraints (via 'constrain') are satisfiable, i.e., that
-- the proof involving these constraints is not passing vacuously. Here is an example. Consider the following
-- predicate:
--
-- >>> let pred = do { x <- forall "x"; constrain $ x .< x; return $ x .>= (5 :: SWord8) }
--
-- This predicate asserts that all 8-bit values are larger than 5, subject to the constraint that the
-- values considered satisfy @x .< x@, i.e., they are less than themselves. Since there are no values that
-- satisfy this constraint, the proof will pass vacuously:
--
-- >>> prove pred
-- Q.E.D.
--
-- We can use 'isVacuous' to make sure to see that the pass was vacuous:
--
-- >>> isVacuous pred
-- True
--
-- While the above example is trivial, things can get complicated if there are multiple constraints with
-- non-straightforward relations; so if constraints are used one should make sure to check the predicate
-- is not vacuously true. Here's an example that is not vacuous:
--
--  >>> let pred' = do { x <- forall "x"; constrain $ x .> 6; return $ x .>= (5 :: SWord8) }
--
-- This time the proof passes as expected:
--
--  >>> prove pred'
--  Q.E.D.
--
-- And the proof is not vacuous:
--
--  >>> isVacuous pred'
--  False
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith defaultSMTCfg

-- Decision procedures (with optional timeout)
checkTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
checkTheorem mbTo p = do r <- pr p
                         case r of
                           ThmResult (Unsatisfiable _) -> return $ Just True
                           ThmResult (Satisfiable _ _) -> return $ Just False
                           ThmResult (TimeOut _)       -> return Nothing
                           _                           -> error $ "SBV.isTheorem: Received:\n" ++ show r
   where pr = maybe prove (\i -> proveWith (defaultSMTCfg{timeOut = Just i})) mbTo

checkSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
checkSatisfiable mbTo p = do r <- s p
                             case r of
                               SatResult (Satisfiable _ _) -> return $ Just True
                               SatResult (Unsatisfiable _) -> return $ Just False
                               SatResult (TimeOut _)       -> return Nothing
                               _                           -> error $ "SBV.isSatisfiable: Received: " ++ show r
   where s = maybe sat (\i -> satWith defaultSMTCfg{timeOut = Just i}) mbTo

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
        (_, _, _, smtLibPgm) <- simulate cvt defaultSMTCfg False comments a
        return $ show smtLibPgm ++ "\n"

-- | Proves the predicate using the given SMT-solver
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith config a = simulate cvt config False [] a >>= callSolver False "Checking Theoremhood.." ThmResult config
  where cvt = if useSMTLib2 config then toSMTLib2 else toSMTLib1

-- | Find a satisfying assignment using the given SMT-solver
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith config a = simulate cvt config True [] a >>= callSolver True "Checking Satisfiability.." SatResult config
  where cvt = if useSMTLib2 config then toSMTLib2 else toSMTLib1

-- | Determine if the constraints are vacuous using the given SMT-solver
isVacuousWith :: Provable a => SMTConfig -> a -> IO Bool
isVacuousWith config a = do
        Result ub tr uic is cs ts as uis ax asgn cstr _ <- runSymbolic True $ forAll_ a >>= output
        case cstr of
           [] -> return False -- no constraints, no need to check
           _  -> do let is'  = [(EX, i) | (_, i) <- is] -- map all quantifiers to "exists" for the constraint check
                        res' = Result ub tr uic is' cs ts as uis ax asgn cstr [trueSW]
                        cvt  = if useSMTLib2 config then toSMTLib2 else toSMTLib1
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
        res <- timeIf isTiming "problem construction" $ runSymbolic isSat $ forAll_ predicate >>= output
        msg $ "Generated symbolic trace:\n" ++ show res
        msg "Translating to SMT-Lib.."
        runProofOn converter config isSat comments res

runProofOn :: SMTLibConverter -> SMTConfig -> Bool -> [String] -> Result -> IO ([(Quantifier, NamedSymVar)], [(String, UnintKind)], [Either SW (SW, [SW])], SMTLibPgm)
runProofOn converter config isSat comments res =
        let isTiming = timing config
        in case res of
             Result hasInfPrec _qcInfo _codeSegs is consts tbls arrs uis axs pgm cstrs [o@(SW (False, Size (Just 1)) _)] ->
               timeIf isTiming "translation" $ let uiMap     = catMaybes (map arrayUIKind arrs) ++ map unintFnUIKind uis
                                                   skolemMap = skolemize (if isSat then is else map flipQ is)
                                                        where flipQ (ALL, x) = (EX, x)
                                                              flipQ (EX, x)  = (ALL, x)
                                                              skolemize :: [(Quantifier, NamedSymVar)] -> [Either SW (SW, [SW])]
                                                              skolemize qinps = go qinps ([], [])
                                                                where go []                   (_,  sofar) = reverse sofar
                                                                      go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                                                                      go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)
                                               in return (is, uiMap, skolemMap, converter hasInfPrec isSat comments is skolemMap consts tbls arrs uis axs pgm cstrs o)
             Result _hasInfPrec _qcInfo _codeSegs _is _consts _tbls _arrs _uis _axs _pgm _cstrs os -> case length os of
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
