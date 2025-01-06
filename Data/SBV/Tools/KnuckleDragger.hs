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
{-# LANGUAGE TypeAbstractions           #-}

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
       , Inductive(..)
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

-- | Bring an IO proof into current proof context.
use :: IO Proof -> KD Proof
use = liftIO

-- | A class for doing equational reasoning style chained proofs. Use 'chainLemma' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class ChainLemma steps step | steps -> step where

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
  makeSteps :: steps -> [step]
  makeInter :: steps -> step -> step -> SBool

  chainLemma nm p steps by   = ask >>= \cfg -> chainLemmaWith   cfg nm p steps by
  chainTheorem nm p steps by = ask >>= \cfg -> chainTheoremWith cfg nm p steps by
  chainLemmaWith             = chainGeneric False
  chainTheoremWith           = chainGeneric True

  chainGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof
  chainGeneric taggedTheorem cfg nm result steps base = do
        liftIO $ putStrLn $ "Chain: " ++ nm
        let proofSteps = makeSteps steps
            len        = length proofSteps

        when (len == 1) $
         error $ unlines $ [ "Incorrect use of chainLemma on " ++ show nm ++ ":"
                           , "**   There must be either none, or at least two steps."
                           , "**   Was given only one step."
                           ]

        go (1 :: Int) base (zipWith (makeInter steps) proofSteps (drop 1 proofSteps))

     where -- if cfg has a transcript, make sure the file is suffixed appropriately
           mkCfg i = cfg{transcript = unique <$> transcript cfg}
             where unique f = "chainLemma_" ++ show i ++ "_" ++ f

           go _ sofar []
              | taggedTheorem = theoremWith cfg nm result sofar
              | True          = lemmaWith   cfg nm result sofar
           go i sofar (p:ps)
            | True
            = do step <- lemmaGen (mkCfg i) "Lemma" ([nm, show i]) p sofar
                 go (i+1) (step : sofar) ps

-- | Chaining lemmas that depend on a single quantified variable.
instance (SymVal a, EqSymbolic z) => ChainLemma (SBV a -> [z]) (SBV a -> z) where
   makeSteps steps = [\a -> steps a !! i | i <- [0 .. length (steps undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) -> x a .== y a

-- | Chaining lemmas that depend on two quantified variables.
instance (SymVal a, SymVal b, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> [z]) (SBV a -> SBV b -> z) where
   makeSteps steps = [\a b -> steps a b !! i | i <- [0 .. length (steps undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) -> x a b .== y a b

-- | Chaining lemmas that depend on three quantified variables.
instance (SymVal a, SymVal b, SymVal c, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> [z]) (SBV a -> SBV b -> SBV c -> z) where
   makeSteps steps = [\a b c -> steps a b c !! i | i <- [0 .. length (steps undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> x a b c .== y a b c

-- | Chaining lemmas that depend on four quantified variables.
instance (SymVal a, SymVal b, SymVal c, SymVal d, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> [z]) (SBV a -> SBV b -> SBV c -> SBV d -> z) where
   makeSteps steps = [\a b c d -> steps a b c d !! i | i <- [0 .. length (steps undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) -> x a b c d .== y a b c d

-- | Chaining lemmas that depend on five quantified variables.
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> [z]) (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> z) where
   makeSteps steps = [\a b c d e -> steps a b c d e !! i | i <- [0 .. length (steps undefined undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) (Forall @"e" e) -> x a b c d e .== y a b c d e

-- | Chaining lemmas that depend on a single quantified variable. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} SymVal a => ChainLemma (SBV a -> [SBool]) (SBV a -> SBool) where
   makeSteps steps = [\a -> steps a !! i | i <- [0 .. length (steps undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) -> x a .=> y a

-- | Chaining lemmas that depend on two quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b) => ChainLemma (SBV a -> SBV b -> [SBool]) (SBV a -> SBV b -> SBool) where
   makeSteps steps = [\a b -> steps a b !! i | i <- [0 .. length (steps undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) -> x a b .=> y a b

-- | Chaining lemmas that depend on three quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b, SymVal c) => ChainLemma (SBV a -> SBV b -> SBV c -> [SBool]) (SBV a -> SBV b -> SBV c -> SBool) where
   makeSteps steps = [\a b c -> steps a b c !! i | i <- [0 .. length (steps undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> x a b c .=> y a b c

-- | Chaining lemmas that depend on four quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b, SymVal c, SymVal d) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> [SBool]) (SBV a -> SBV b -> SBV c -> SBV d -> SBool) where
   makeSteps steps = [\a b c d -> steps a b c d !! i | i <- [0 .. length (steps undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) -> x a b c d .=> y a b c d

-- | Chaining lemmas that depend on five quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> [SBool]) (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBool) where
   makeSteps steps = [\a b c d e -> steps a b c d e !! i | i <- [0 .. length (steps undefined undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) (Forall @"e" e) -> x a b c d e .=> y a b c d e

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

   inductGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof

-- Capture the general flow after a checkSat. We run the sat case if model is empty.
checkSatThen :: (MonadIO m, MonadQuery m) => String -> Maybe (m a) -> m a -> m a
checkSatThen nm mbSat unsat = do
   r <- checkSat
   case r of
    Unk    -> unknown
    Sat    -> cex
    DSat{} -> cex
    Unsat  -> unsat
 where die = error "Failed"

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

-- | Induction over 'SInteger'.
instance EqSymbolic z => Inductive (Forall nm Integer -> SBool) (SInteger -> ([z], [z])) where
   inductGeneric tagTheorem cfg@SMTConfig{verbose} nm qResult steps helpers = liftIO $ do
        putStrLn $ "Inductive " ++ (if tagTheorem then "theorem" else "lemma") ++ ": " ++ nm
        runSMTWith cfg schema

     where result = qResult . Forall

           liftKD     = liftIO . runKDWith cfg
           mkPairs xs = zipWith (\(i, l) (j, r) -> ((i, j), l .== r)) xs (drop 1 xs)

           (ros, modulo) = calculateRootOfTrust nm helpers

           schema = do
              mapM_ (constrain . getProof) helpers

              -- Do the dummy call trick here so all the uninterpreted functions
              -- are properly registered. Hopefully this is enough!
              dummy <- internalVariable KUnbounded
              let rdummy = result dummy
              constrain $ rdummy .== rdummy

              query $ do

                -- Base case first
                inNewAssertionStack $ do
                   let caseName = [nm, "Base"]
                   tab <- liftKD $ start verbose "Base" caseName
                   constrain $ sNot (result 0)
                   checkSatThen (intercalate "." caseName)
                                (Just (io $ putStrLn "Property fails for n = 0."))
                                (liftKD $ finish ("Q.E.D." ++ modulo) tab)

                -- Induction
                k <- freshVar "k"
                constrain $ k .>= 0
                constrain $ result k

                let (ls, rs) = steps k
                    taggedLs = zip ['L' : show i | i <- [(1 :: Int) ..]] ls
                    taggedRs = zip ['R' : show i | i <- [(1 :: Int) ..]] rs
                    lPairs   = mkPairs taggedLs
                    rPairs   = mkPairs taggedRs
                    pairs    =  lPairs ++ rPairs
                             ++ mkPairs (take 1 (reverse taggedLs) ++ take 1 (reverse taggedRs))

                    loop accum (((i, j), s):ss) = do
                       let caseName = [nm, i ++ " vs " ++ j]

                       tab <- liftKD $ start verbose "Help" caseName

                       inNewAssertionStack $ do
                          constrain accum
                          constrain $ sNot s

                          checkSatThen (intercalate "." caseName) Nothing $ liftKD $ finish ("Q.E.D." ++ modulo) tab

                       loop (accum .&& s) ss

                    loop accum [] = pure accum

                -- Get the schema
                indSchema <- loop sTrue pairs

                -- Do the final proof:
                let caseName = [nm, "Step"]

                tab <- liftKD $ start verbose "Step" caseName

                constrain indSchema

                -- Normal induction would be k+1; but we're doing full induction, so also go k-1
                constrain $ sNot $   observeIf not "P(k+1)" (result (k+1))
                                 .&& observeIf not "P(k-1)" (result (k-1))

                checkSatThen (intercalate "." caseName) Nothing $ do
                  liftKD $ finish ("Q.E.D." ++ modulo) tab
                  pure $ Proof { rootOfTrust = ros
                               , isUserAxiom = False
                               , getProof    = label nm $ quantifiedBool qResult
                               , proofName   = nm
                               }

{-
-- | Given a predicate, return an induction principle for it. Typically, we only have one viable
-- induction principle for a given type, but we allow for alternative ones.
class Inductive a where
  induct     :: a -> Proof
  inductAlt1 :: a -> Proof
  inductAlt2 :: a -> Proof

  -- The second and third principles are the same as first by default, unless we provide them explicitly.
  inductAlt1 = induct
  inductAlt2 = induct

-- | Induction over SInteger. We provide various induction principles here: The first one
-- is over naturals, will only prove predicates that explicitly restrict the argument to >= 0.
-- The second and third ones are induction over the entire range of integers, two different
-- principles that might work better for different problems.
instance Inductive (SInteger -> SBool) where

   -- | Induction over naturals. Will prove predicates of the form @\n -> n >= 0 .=> predicate n@.
   induct p = internalAxiom "Nat.induct" principle
      where qb = quantifiedBool

            principle =          p 0
                             .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                      .=> qb -----------------------------------------------------
                                 (\(Forall n) -> n .>= 0 .=> p n)


   -- | Induction over integers, using the strategy that @P(n)@ is equivalent to @P(n+1)@
   -- (i.e., not just @P(n) => P(n+1)@), thus covering the entire range.
   inductAlt1 p = internalAxiom "Integer.inductAlt1" principle
     where qb = quantifiedBool

           principle =          p 0
                            .&& qb (\(Forall i) -> p i .== p (i+1))
                     .=> qb ---------------------------------------
                                (\(Forall i) -> p i)

   -- | Induction over integers, using the strategy that @P(n) => P(n+1)@ and @P(n) => P(n-1)@.
   inductAlt2 p = internalAxiom "Integer.inductAlt2" principle
     where qb = quantifiedBool

           principle =          p 0
                            .&& qb (\(Forall i) -> p i .=> p (i+1) .&& p (i-1))
                     .=> qb ---------------------------------------------------
                                (\(Forall i) -> p i)

-- | Induction over two argument predicates, with the last argument SInteger.
instance SymVal a => Inductive (SBV a -> SInteger -> SBool) where
  induct p = internalAxiom "Nat.induct2" principle
     where qb a = quantifiedBool a

           principle =          qb (\(Forall a) -> p a 0)
                            .&& qb (\(Forall a) (Forall n) -> (n .>= 0 .&& p a n) .=> p a (n+1))
                     .=> qb --------------------------------------------------------------------
                                (\(Forall a) (Forall n) -> n .>= 0 .=> p a n)

-- | Induction over three argument predicates, with last argument SInteger.
instance (SymVal a, SymVal b) => Inductive (SBV a -> SBV b -> SInteger -> SBool) where
  induct p = internalAxiom "Nat.induct3" principle
     where qb a = quantifiedBool a

           principle =          qb (\(Forall a) (Forall b) -> p a b 0)
                            .&& qb (\(Forall a) (Forall b) (Forall n) -> (n .>= 0 .&& p a b n) .=> p a b (n+1))
                     .=> qb -----------------------------------------------------------------------------------
                                (\(Forall a) (Forall b) (Forall n) -> n .>= 0 .=> p a b n)

-- | Induction over four argument predicates, with last argument SInteger.
instance (SymVal a, SymVal b, SymVal c) => Inductive (SBV a -> SBV b -> SBV c -> SInteger -> SBool) where
  induct p = internalAxiom "Nat.induct4" principle
     where qb a = quantifiedBool a

           principle =          qb (\(Forall a) (Forall b) (Forall c) -> p a b c 0)
                            .&& qb (\(Forall a) (Forall b) (Forall c) (Forall n) -> (n .>= 0 .&& p a b c n) .=> p a b c (n+1))
                     .=> qb --------------------------------------------------------------------------------------------------
                                (\(Forall a) (Forall b) (Forall c) (Forall n) -> n .>= 0 .=> p a b c n)


-- | Induction over lists
instance SymVal a => Inductive (SList a -> SBool) where
  induct p = internalAxiom "List(a).induct" principle
    where qb a = quantifiedBool a

          principle =          p SL.nil
                           .&& qb (\(Forall x) (Forall xs) -> p xs .=> p (x SL..: xs))
                    .=> qb -----------------------------------------------------------
                               (\(Forall xs) -> p xs)

-- | Induction over two argument predicates, with last argument a list.
instance (SymVal a, SymVal e) => Inductive (SBV a -> SList e -> SBool) where
  induct p = internalAxiom "List(a).induct2" principle
    where qb a = quantifiedBool a

          principle =          qb (\(Forall a) -> p a SL.nil)
                           .&& qb (\(Forall a) (Forall e) (Forall es) -> p a es .=> p a (e SL..: es))
                    .=> qb --------------------------------------------------------------------------
                               (\(Forall a) (Forall es) -> p a es)

-- | Induction over three argument predicates, with last argument a list.
instance (SymVal a, SymVal b, SymVal e) => Inductive (SBV a -> SBV b -> SList e -> SBool) where
  induct p = internalAxiom "List(a).induct3" principle
    where qb a = quantifiedBool a

          principle =          qb (\(Forall a) (Forall b) -> p a b SL.nil)
                           .&& qb (\(Forall a) (Forall b) (Forall e) (Forall es) -> p a b es .=> p a b (e SL..: es))
                    .=> qb -----------------------------------------------------------------------------------------
                               (\(Forall a) (Forall b) (Forall xs) -> p a b xs)

-- | Induction over four argument predicates, with last argument a list.
instance (SymVal a, SymVal b, SymVal c, SymVal e) => Inductive (SBV a -> SBV b -> SBV c -> SList e -> SBool) where
  induct p = internalAxiom "List(a).induct4" principle
    where qb a = quantifiedBool a

          principle =          qb (\(Forall a) (Forall b) (Forall c) -> p a b c SL.nil)
                           .&& qb (\(Forall a) (Forall b) (Forall c) (Forall e) (Forall es) -> p a b c es .=> p a b c (e SL..: es))
                    .=> qb --------------------------------------------------------------------------------------------------------
                               (\(Forall a) (Forall b) (Forall c) (Forall xs) -> p a b c xs)
-}
