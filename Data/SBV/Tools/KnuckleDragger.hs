-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KnuckleDragger
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A lightweight theorem proving like interface, built on top of SBV.
-- Inspired by and modeled after Philip Zucker's tool with the same
-- name, see <http://github.com/philzook58/knuckledragger>.
--
-- See the directory Documentation.SBV.Examples.KnuckleDragger for various examples.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE TypeApplications           #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger (
       -- * Propositions and their proofs
         Proposition, Proof
       -- * Adding axioms/definitions
       , axiom
       -- * Basic proofs
       , lemma,        lemmaWith
       , theorem,      theoremWith
       -- * Chain of reasoning
       , chainLemma,   chainLemmaWith
       , chainTheorem, chainTheoremWith
       -- * Induction
       , induct, inductAlt1, inductAlt2
       , inductiveLemma,   inductiveLemmaWith
       , inductiveTheorem, inductiveTheoremWith
       -- * Faking proofs
       , sorry
       -- * Running KnuckleDragger proofs
       , KD, runKD, runKDWith, use
       ) where

import Data.SBV
import Data.SBV.Core.Data (SolverContext(internalVariable))
import Data.SBV.Core.Symbolic (isEmptyModel)

import Data.SBV.Control.Utils (getConfig)
import Data.SBV.Control hiding (getProof)

import Data.SBV.Tools.KDKernel
import Data.SBV.Tools.KDUtils

import Control.Monad        (when)
import Control.Monad.Trans  (MonadIO, liftIO)
import Control.Monad.Reader (ask)

import Data.List (intercalate)

import qualified Data.SBV.List as SL

import Data.Proxy
import GHC.TypeLits (KnownSymbol, symbolVal)

-- | Bring an IO proof into current proof context.
use :: IO Proof -> KD Proof
use = liftIO

-- | A class for doing equational reasoning style chained proofs. Use 'chainLemma' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class ChainLemma a steps step | steps -> step where

  -- | Prove a property via a series of equality steps, using the default solver.
  -- Let @H@ be a list of already established lemmas. Let @P@ be a property we wanted to prove, named @name@.
  -- Consider a call of the form @chainLemma name P [A, B, C, D] H@. Note that @H@ is
  -- a list of already proven facts, ensured by the type signature. We proceed as follows:
  --
  --    * Prove: @H -> A == B@
  --    * Prove: @H && A == B -> B == C@
  --    * Prove: @H && A == B && B == C -> C == D@
  --    * Prove: @H && A == B && B == C && C == D -> P@
  --    * If all of the above steps succeed, conclude @P@.
  --
  -- Note that if the type of steps (i.e., @A@ .. @D@ above) is 'SBool', then we use implication
  -- as opposed to equality; which better captures line of reasoning.
  --
  -- So, chain-lemma is essentially modus-ponens, applied in a sequence of stepwise equality reasoning in the case of
  -- non-boolean steps.
  --
  -- If there are no helpers given (i.e., if @H@ is empty), then this call is equivalent to 'lemmaWith'.
  -- If @H@ is a singleton, then we bail out. A single step in @H@ indicates a usage mistake, since there's
  -- no sequence of steps to reason about.
  chainLemma :: Proposition a => String -> a -> steps -> [Proof] -> KD Proof

  -- | Same as chainLemma, except tagged as Theorem
  chainTheorem :: Proposition a => String -> a -> steps -> [Proof] -> KD Proof

  -- | Prove a property via a series of equality steps, using the given solver.
  chainLemmaWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof

  -- | Same as chainLemmaWith, except tagged as Theorem
  chainTheoremWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof

  -- | Internal, shouldn't be needed outside the library
  {-# MINIMAL chainSteps #-}
  chainSteps :: a -> steps -> Symbolic (SBool, [SBool])

  chainLemma   nm p steps by = ask >>= \cfg -> chainLemmaWith   cfg nm p steps by
  chainTheorem nm p steps by = ask >>= \cfg -> chainTheoremWith cfg nm p steps by
  chainLemmaWith             = chainGeneric False
  chainTheoremWith           = chainGeneric True

  chainGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof
  chainGeneric tagTheorem cfg@SMTConfig{verbose} nm result steps helpers = liftIO $ runSMTWith cfg $ do

        liftIO $ putStrLn $ "Chain " ++ (if tagTheorem then "theorem" else "lemma") ++ ": " ++ nm

        let (ros, modulo) = calculateRootOfTrust nm helpers
            finish        = finishKD cfg ("Q.E.D." ++ modulo)

        (goal, proofSteps) <- chainSteps result steps

        -- This seemingly unneded constraint makes sure SBV sees the
        -- definitions of any smtFunction calls or uninterpreted functions;
        -- so it's important to keep it here.
        constrain $ goal .== goal

        -- proofSteps is the zipped version; so if it's null then user must've given 0 or 1 steps.
        when (null proofSteps) $
           error $ unlines $ [ "Incorrect use of chainLemma on " ++ show nm ++ ":"
                             , "**   There must be at least two steps."
                             , "**   Was given less than two."
                             ]

        mapM_ (constrain . getProof) helpers

        let go :: Int -> SBool -> [SBool] -> Query Proof
            go _ accum [] = do
                checkSatThen verbose "Result" accum goal ["", ""] Nothing $ \tab -> do
                  finish tab
                  pure Proof { rootOfTrust = ros
                             , isUserAxiom = False
                             , getProof    = label nm $ quantifiedBool result
                             , proofName   = nm
                             }

            go i accum (s:ss) = do
                 checkSatThen verbose "Step  " accum s ["", show i] Nothing finish
                 go (i+1) (s .&& accum) ss

        query $ go (1::Int) sTrue proofSteps

-- | Turn a sequence of steps into a chain of pairs, merged with a function.
mkChainSteps :: (a -> a -> b) -> [a] -> [b]
mkChainSteps f xs = zipWith f xs (drop 1 xs)

-- | Chaining lemmas that depend on a single quantified variable.
instance (KnownSymbol na, SymVal a, EqSymbolic z) => ChainLemma (Forall na a -> SBool) (SBV a -> [z]) z where
   chainSteps result steps = do a <- free (symbolVal (Proxy @na))
                                pure (result (Forall a), mkChainSteps (.==) (steps a))

-- | Chaining lemmas that depend on two quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z)
      => ChainLemma (Forall na a -> Forall nb b -> SBool)
                    (SBV a -> SBV b -> [z])
                    (SBV a -> SBV b -> z) where
   chainSteps result steps = do (a, b) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                                pure (result (Forall a) (Forall b), mkChainSteps (.==) (steps a b))

-- | Chaining lemmas that depend on three quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z)
      => ChainLemma (Forall na a -> Forall nb b -> Forall nc c -> SBool)
                    (SBV a -> SBV b -> SBV c -> [z])
                    (SBV a -> SBV b -> SBV c -> z) where
   chainSteps result steps = do (a, b, c) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                                pure (result (Forall a) (Forall b) (Forall c), mkChainSteps (.==) (steps a b c))

-- | Chaining lemmas that depend on four quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z)
      => ChainLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                    (SBV a -> SBV b -> SBV c -> SBV d -> [z]) (SBV a -> SBV b -> SBV c -> SBV d -> z) where
   chainSteps result steps = do (a, b, c, d) <- (,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                                pure (result (Forall a) (Forall b) (Forall c) (Forall d), mkChainSteps (.==) (steps a b c d))

-- | Chaining lemmas that depend on five quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z)
      => ChainLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool)
                    (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> [z]) (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> z) where
   chainSteps result steps = do (a, b, c, d, e) <- (,,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                                pure (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e), mkChainSteps (.==) (steps a b c d e))

-- | Chaining lemmas that depend on a single quantified variable. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (KnownSymbol na, SymVal a) => ChainLemma (Forall na a -> SBool) (SBV a -> [SBool]) SBool where
   chainSteps result steps = do a <- free (symbolVal (Proxy @na))
                                pure (result (Forall a), mkChainSteps (.=>) (steps a))

-- | Chaining lemmas that depend on two quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b)
      => ChainLemma (Forall na a -> Forall nb b -> SBool)
                    (SBV a -> SBV b -> [SBool])
                    (SBV a -> SBV b -> SBool) where
   chainSteps result steps = do (a, b) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                                pure (result (Forall a) (Forall b), mkChainSteps (.=>) (steps a b))

-- | Chaining lemmas that depend on three quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c)
      => ChainLemma (Forall na a -> Forall nb b -> Forall nc c -> SBool)
                    (SBV a -> SBV b -> SBV c -> [SBool])
                    (SBV a -> SBV b -> SBV c -> SBool) where
   chainSteps result steps = do (a, b, c) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                                pure (result (Forall a) (Forall b) (Forall c), mkChainSteps (.=>) (steps a b c))

-- | Chaining lemmas that depend on four quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d)
      => ChainLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                    (SBV a -> SBV b -> SBV c -> SBV d -> [SBool]) (SBV a -> SBV b -> SBV c -> SBV d -> SBool) where
   chainSteps result steps = do (a, b, c, d) <- (,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                                pure (result (Forall a) (Forall b) (Forall c) (Forall d), mkChainSteps (.=>) (steps a b c d))

-- | Chaining lemmas that depend on five quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e)
      => ChainLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool)
                    (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> [SBool]) (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBool) where
   chainSteps result steps = do (a, b, c, d, e) <- (,,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                                pure (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e), mkChainSteps (.=>) (steps a b c d e))

-- | Captures the schema for an inductive proof
data InductionStrategy = InductionStrategy { inductionBaseCase       :: SBool
                                           , inductiveHypothesis     :: SBool
                                           , inductionHelperSteps    :: [(String, SBool)]
                                           , inductionBaseFailureMsg :: String
                                           , inductiveStep           :: SBool
                                           }

-- | A class for doing inductive proofs, with the possibility of explicit steps.
class Inductive a steps where
   -- | Inductively prove a lemma, using the default config.
   inductiveLemma :: Proposition a => String -> a -> steps -> [Proof] -> KD Proof

   -- | Inductively prove a theorem. Same as 'inductiveLemma', but tagged as a theorem, using the default config.
   inductiveTheorem :: Proposition a => String -> a -> steps -> [Proof] -> KD Proof

   -- | Same as 'inductiveLemma', but with the given solver configuration.
   inductiveLemmaWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof

   -- | Same as 'inductiveTheorem, but with the given solver configuration.
   inductiveTheoremWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof

   inductiveLemma   nm p steps by = ask >>= \cfg -> inductiveLemmaWith   cfg nm p steps by
   inductiveTheorem nm p steps by = ask >>= \cfg -> inductiveTheoremWith cfg nm p steps by
   inductiveLemmaWith             = inductGeneric False
   inductiveTheoremWith           = inductGeneric True

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL inductionStrategy #-}
   inductionStrategy :: Proposition a => a -> steps -> Symbolic InductionStrategy

   inductGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof
   inductGeneric tagTheorem cfg@SMTConfig{verbose} nm qResult steps helpers = liftIO $ do
        putStrLn $ "Inductive " ++ (if tagTheorem then "theorem" else "lemma") ++ ": " ++ nm
        runSMTWith cfg $ do
           mapM_ (constrain . getProof) helpers

           let (ros, modulo) = calculateRootOfTrust nm helpers
               finish       = finishKD cfg ("Q.E.D." ++ modulo)

           InductionStrategy { inductionBaseCase
                             , inductiveHypothesis
                             , inductionHelperSteps
                             , inductionBaseFailureMsg
                             , inductiveStep
                             } <- inductionStrategy qResult steps

           query $ do

             -- Base case first
            checkSatThen verbose
                         "Base"
                         sTrue
                         inductionBaseCase
                         [nm, "Base"]
                         (Just (io $ putStrLn inductionBaseFailureMsg))
                         finish

            constrain inductiveHypothesis

            let loop accum ((snm, s):ss) = do
                    checkSatThen verbose "Help" accum s [nm, snm] Nothing finish
                    loop (accum .&& s) ss

                loop accum [] = pure accum

            -- Get the schema
            indSchema <- loop sTrue inductionHelperSteps

            -- Do the final proof:
            checkSatThen verbose "Step" indSchema inductiveStep [nm, "Step"] Nothing $ \tab -> do
              finish tab
              pure $ Proof { rootOfTrust = ros
                           , isUserAxiom = False
                           , getProof    = label nm $ quantifiedBool qResult
                           , proofName   = nm
                           }

-- Capture the general flow after a checkSat. We run the sat case if model is empty.
checkSatThen :: (SolverContext m, MonadIO m, MonadQuery m)
   => Bool               -- ^ verbose
   -> String             -- ^ tag
   -> SBool              -- ^ context
   -> SBool              -- ^ what we want to prove
   -> [String]           -- ^ sub-proof
   -> Maybe (m a)        -- ^ special code to run if model is empty (if any)
   -> (Int -> IO a)      -- ^ what to do when unsat, with the tab amount
   -> m a
checkSatThen verbose tag ctx cond nms mbSat unsat = inNewAssertionStack $ do
   tab <- liftIO $ startKD verbose tag nms
   constrain ctx
   constrain $ sNot cond
   r <- checkSat
   case r of
    Unk    -> unknown
    Sat    -> cex
    DSat{} -> cex
    Unsat  -> liftIO $ unsat tab
 where die = error "Failed"

       nm = intercalate "." (filter (not . null) nms)

       unknown = do r <- getUnknownReason
                    liftIO $ do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                                putStrLn $ "\n*** Solver reported: " ++ show r
                                die

       cex = do liftIO $ putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                model <- getModel
                case (isEmptyModel model, mbSat) of
                  (True,  Just act) -> act >> die
                  _                 -> do res <- Satisfiable <$> getConfig <*> pure model
                                          liftIO $ print $ ThmResult res
                                          die

-- | Create a sequence of proof-obligations from the inductive steps
pairInductiveSteps :: EqSymbolic a => ([a], [a]) -> [(String, SBool)]
pairInductiveSteps (ls, rs) = pairs
  where mkPairs xs = zipWith (\(i, l) (j, r) -> (i ++ " vs " ++  j, l .== r)) xs (drop 1 xs)
        taggedLs = zip ['L' : show i | i <- [(1 :: Int) ..]] ls
        taggedRs = zip ['R' : show i | i <- [(1 :: Int) ..]] rs
        lPairs   = mkPairs taggedLs
        rPairs   = mkPairs taggedRs
        pairs    =  lPairs
                 ++ rPairs
                 ++ mkPairs (take 1 (reverse taggedLs) ++ take 1 (reverse taggedRs))

-- | Saturate the given predicate; i.e., we run it on dummy-variables and assert equality of the self,
-- which ensures the uninterpreted/smtDefine functions to get recorded.
saturate :: (SolverContext m, EqSymbolic a) => a -> m ()
saturate d = constrain $ d .== d

-- | Induction over 'SInteger'.
instance   (KnownSymbol nk, EqSymbolic z)
        => Inductive (Forall nk Integer -> SBool)
                     (SInteger -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate k = qResult (Forall k)
           nk          = symbolVal (Proxy @nk)

       k <- free nk
       constrain $ k .>= 0

       saturate =<< predicate <$> internalVariable (kindOf k)

       pure InductionStrategy {
                inductionBaseCase       = predicate 0
              , inductiveHypothesis     = predicate k
              , inductionHelperSteps    = pairInductiveSteps (steps k)
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           =     observeIf not ("P(" ++ nk ++ "+1)") (predicate (k+1))
                                          .&& observeIf not ("P(" ++ nk ++ "-1)") (predicate (k-1))
              }

-- | Induction over 'SInteger' taking an extra argument.
instance    ( KnownSymbol na, SymVal a
            , KnownSymbol nk, EqSymbolic z)
         => Inductive (Forall na a -> Forall nk Integer -> SBool)
                      (SBV a -> SInteger -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a k = qResult (Forall a) (Forall k)
           na            = symbolVal (Proxy @na)
           nk            = symbolVal (Proxy @nk)

       a <- free na
       k <- free nk
       constrain $ k .>= 0

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf k)


       pure InductionStrategy {
                inductionBaseCase       = predicate a 0
              , inductiveHypothesis     = predicate a k
              , inductionHelperSteps    = pairInductiveSteps (steps a k)
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           =     observeIf not ("P(" ++ nk ++ "+1)") (predicate a (k+1))
                                          .&& observeIf not ("P(" ++ nk ++ "-1)") (predicate a (k-1))
              }

-- | Induction over 'SInteger' taking two extra arguments.
instance    ( KnownSymbol na, SymVal a
            , KnownSymbol nb, SymVal b
            , KnownSymbol nk, EqSymbolic z)
         => Inductive (Forall na a -> Forall nb b -> Forall nk Integer -> SBool)
                      (SBV a -> SBV b -> SInteger -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a b k = qResult (Forall a) (Forall b) (Forall k)
           na              = symbolVal (Proxy @na)
           nb              = symbolVal (Proxy @nb)
           nk              = symbolVal (Proxy @nk)

       a <- free na
       b <- free nb
       k <- free nk
       constrain $ k .>= 0

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf b)
                              <*> internalVariable (kindOf k)


       pure InductionStrategy {
                inductionBaseCase       = predicate a b 0
              , inductiveHypothesis     = predicate a b k
              , inductionHelperSteps    = pairInductiveSteps (steps a b k)
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           =     observeIf not ("P(" ++ nk ++ "+1)") (predicate a b (k+1))
                                          .&& observeIf not ("P(" ++ nk ++ "-1)") (predicate a b (k-1))
              }

-- | Induction over 'SInteger' taking three extra arguments.
instance    ( KnownSymbol na, SymVal a
            , KnownSymbol nb, SymVal b
            , KnownSymbol nc, SymVal c
            , KnownSymbol nk, EqSymbolic z)
         => Inductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nk Integer -> SBool)
                      (SBV a -> SBV b -> SBV c -> SInteger -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a b c k = qResult (Forall a) (Forall b) (Forall c) (Forall k)
           na                = symbolVal (Proxy @na)
           nb                = symbolVal (Proxy @nb)
           nc                = symbolVal (Proxy @nc)
           nk                = symbolVal (Proxy @nk)

       a <- free na
       b <- free nb
       c <- free nc
       k <- free nk
       constrain $ k .>= 0

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf b)
                              <*> internalVariable (kindOf c)
                              <*> internalVariable (kindOf k)


       pure InductionStrategy {
                inductionBaseCase       = predicate a b c 0
              , inductiveHypothesis     = predicate a b c k
              , inductionHelperSteps    = pairInductiveSteps (steps a b c k)
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           =     observeIf not ("P(" ++ nk ++ "+1)") (predicate a b c (k+1))
                                          .&& observeIf not ("P(" ++ nk ++ "-1)") (predicate a b c (k-1))
              }

-- | Induction over 'SInteger' taking four extra arguments.
instance    ( KnownSymbol na, SymVal a
            , KnownSymbol nb, SymVal b
            , KnownSymbol nc, SymVal c
            , KnownSymbol nd, SymVal d
            , KnownSymbol nk, EqSymbolic z)
         => Inductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall nk Integer -> SBool)
                      (SBV a -> SBV b -> SBV c -> SBV d -> SInteger -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a b c d k = qResult (Forall a) (Forall b) (Forall c) (Forall d) (Forall k)
           na                  = symbolVal (Proxy @na)
           nb                  = symbolVal (Proxy @nb)
           nc                  = symbolVal (Proxy @nc)
           nd                  = symbolVal (Proxy @nd)
           nk                  = symbolVal (Proxy @nk)

       a <- free na
       b <- free nb
       c <- free nc
       d <- free nd
       k <- free nk
       constrain $ k .>= 0

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf b)
                              <*> internalVariable (kindOf c)
                              <*> internalVariable (kindOf d)
                              <*> internalVariable (kindOf k)


       pure InductionStrategy {
                inductionBaseCase       = predicate a b c d 0
              , inductiveHypothesis     = predicate a b c d k
              , inductionHelperSteps    = pairInductiveSteps (steps a b c d k)
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           =     observeIf not ("P(" ++ nk ++ "+1)") (predicate a b c d (k+1))
                                          .&& observeIf not ("P(" ++ nk ++ "-1)") (predicate a b c d (k-1))
              }

-- Given a user name for the list, get a name for the element, in the most suggestive way possible
--   xs  -> x
--   xss -> xs
--   foo -> fooElt
singular :: String -> String
singular n = case reverse n of
               's':_:_ -> init n
               _       -> n ++ "Elt"

-- | Induction over 'SList'.
instance   (KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall nk [k] -> SBool)
                     (SBV k -> SList k -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate k = qResult (Forall k)
           nks         = symbolVal (Proxy @nk)
           nk          = singular nks

       k  <- free nk
       ks <- free nks

       saturate =<< predicate <$> internalVariable (kindOf ks)

       pure InductionStrategy {
                inductionBaseCase       = predicate SL.nil
              , inductiveHypothesis     = predicate ks
              , inductionHelperSteps    = pairInductiveSteps (steps k ks)
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate (k SL..: ks))
              }

-- | Induction over 'SList' taking an extra argument
instance   ( KnownSymbol na, SymVal a
           , KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall na a -> Forall nk [k] -> SBool)
                     (SBV a -> SBV k -> SList k -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a k = qResult (Forall a) (Forall k)
           na            = symbolVal (Proxy @na)
           nks           = symbolVal (Proxy @nk)
           nk            = singular nks

       a  <- free na
       k  <- free nk
       ks <- free nks

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf ks)

       pure InductionStrategy {
                inductionBaseCase       = predicate a SL.nil
              , inductiveHypothesis     = predicate a ks
              , inductionHelperSteps    = pairInductiveSteps (steps a k ks)
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate a (k SL..: ks))
              }

-- | Induction over 'SList' taking two extra arguments
instance   ( KnownSymbol na, SymVal a
           , KnownSymbol nb, SymVal b
           , KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall na a -> Forall nb b -> Forall nk [k] -> SBool)
                     (SBV a -> SBV b -> SBV k -> SList k -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a b k = qResult (Forall a) (Forall b) (Forall k)
           na              = symbolVal (Proxy @na)
           nb              = symbolVal (Proxy @nb)
           nks             = symbolVal (Proxy @nk)
           nk              = singular nks

       a  <- free na
       b  <- free nb
       k  <- free nk
       ks <- free nks

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf b)
                              <*> internalVariable (kindOf ks)

       pure InductionStrategy {
                inductionBaseCase       = predicate a b SL.nil
              , inductiveHypothesis     = predicate a b ks
              , inductionHelperSteps    = pairInductiveSteps (steps a b k ks)
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate a b (k SL..: ks))
              }

-- | Induction over 'SList' taking three extra arguments
instance   ( KnownSymbol na, SymVal a
           , KnownSymbol nb, SymVal b
           , KnownSymbol nc, SymVal c
           , KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nk [k] -> SBool)
                     (SBV a -> SBV b -> SBV c -> SBV k -> SList k -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a b c k = qResult (Forall a) (Forall b) (Forall c) (Forall k)
           na                = symbolVal (Proxy @na)
           nb                = symbolVal (Proxy @nb)
           nc                = symbolVal (Proxy @nc)
           nks               = symbolVal (Proxy @nk)
           nk                = singular nks

       a  <- free na
       b  <- free nb
       c  <- free nc
       k  <- free nk
       ks <- free nks

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf b)
                              <*> internalVariable (kindOf c)
                              <*> internalVariable (kindOf ks)

       pure InductionStrategy {
                inductionBaseCase       = predicate a b c SL.nil
              , inductiveHypothesis     = predicate a b c ks
              , inductionHelperSteps    = pairInductiveSteps (steps a b c k ks)
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate a b c (k SL..: ks))
              }

-- | Induction over 'SList' taking four extra arguments
instance   ( KnownSymbol na, SymVal a
           , KnownSymbol nb, SymVal b
           , KnownSymbol nc, SymVal c
           , KnownSymbol nd, SymVal d
           , KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall nk [k] -> SBool)
                     (SBV a -> SBV b -> SBV c -> SBV d -> SBV k -> SList k -> ([z], [z]))
 where
   inductionStrategy qResult steps = do
       let predicate a b c d k = qResult (Forall a) (Forall b) (Forall c) (Forall d) (Forall k)
           na                  = symbolVal (Proxy @na)
           nb                  = symbolVal (Proxy @nb)
           nc                  = symbolVal (Proxy @nc)
           nd                  = symbolVal (Proxy @nd)
           nks                 = symbolVal (Proxy @nk)
           nk                  = singular nks

       a  <- free na
       b  <- free nb
       c  <- free nc
       d  <- free nd
       k  <- free nk
       ks <- free nks

       saturate =<< predicate <$> internalVariable (kindOf a)
                              <*> internalVariable (kindOf b)
                              <*> internalVariable (kindOf c)
                              <*> internalVariable (kindOf d)
                              <*> internalVariable (kindOf ks)

       pure InductionStrategy {
                inductionBaseCase       = predicate a b c d SL.nil
              , inductiveHypothesis     = predicate a b c d ks
              , inductionHelperSteps    = pairInductiveSteps (steps a b c d k ks)
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate a b c d (k SL..: ks))
              }
