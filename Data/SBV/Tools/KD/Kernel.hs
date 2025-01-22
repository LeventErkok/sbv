-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KD.Kernel
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Kernel of the KnuckleDragger prover API.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KD.Kernel (
         Proposition,  Proof(..)
       , axiom
       , lemma,   lemmaWith,   lemmaGen
       , theorem, theoremWith
       , InductionTactic(..)
       , sorry
       , checkSatThen
       ) where

import Control.Monad.Trans  (liftIO, MonadIO)

import Data.List (intercalate)

import Data.SBV
import Data.SBV.Core.Data (Constraint, SolverContext)
import Data.SBV.Core.Symbolic (isEmptyModel)
import Data.SBV.Control hiding (getProof)
import Data.SBV.Control.Utils (getConfig)

import qualified Data.SBV.List as SL

import Data.SBV.Tools.KD.Utils

-- | A proposition is something SBV is capable of proving/disproving. We capture this
-- with a set of constraints. This type might look scary, but for the most part you
-- can ignore it and treat it as anything you can pass to 'prove' or 'sat' in SBV.
type Proposition a = ( QNot a
                     , QuantifiedBool a
                     , Skolemize (NegatesTo a)
                     , QuantifiedBool (SkolemsTo (NegatesTo a))
                     , Constraint  Symbolic  (SkolemsTo (NegatesTo a))
                     )

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols. Note that we perform no checks on these propositions,
-- if you assert nonsense, then you get nonsense back. So, calls to 'axiom' should be limited to
-- definitions, or basic axioms (like commutativity, associativity) of uninterpreted function symbols.
axiom :: Proposition a => String -> a -> KD Proof
axiom nm p = do _ <- liftIO $ startKD True "Axiom" [nm]
                pure (internalAxiom nm p) { isUserAxiom = True }

-- | Internal axiom generator; so we can keep truck of KnuckleDrugger's trusted axioms, vs. user given axioms.
-- Not exported.
internalAxiom :: Proposition a => String -> a -> Proof
internalAxiom nm p = Proof { rootOfTrust = None
                           , isUserAxiom = False
                           , getProof    = label nm (quantifiedBool p)
                           , proofName   = nm
                           }

-- | A manifestly false theorem. This is useful when we want to prove a theorem that the underlying solver
-- cannot deal with, or if we want to postpone the proof for the time being. KnuckleDragger will keep
-- track of the uses of 'sorry' and will print them appropriately while printing proofs.
sorry :: Proof
sorry = Proof { rootOfTrust = Self
              , isUserAxiom = False
              , getProof    = label "sorry" (quantifiedBool p)
              , proofName   = "sorry"
              }
  where -- ideally, I'd rather just use 
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall (x :: SBool)) = label "SORRY: KnuckleDragger, proof uses \"sorry\"" x

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> [String] -> a -> [Proof] -> KD Proof
lemmaGen cfg@SMTConfig{verbose} tag nms inputProp by = liftIO $ runSMTWith cfg $ go
  where go  = do mapM_ (constrain . getProof) by
                 query $ checkSatThen verbose tag sTrue inputProp nms Nothing good

        -- What to do if all goes well
        good tab = do liftIO $ finishKD cfg ("Q.E.D." ++ modulo) tab
                      pure Proof { rootOfTrust = ros
                                 , isUserAxiom = False
                                 , getProof    = label nm (quantifiedBool inputProp)
                                 , proofName   = nm
                                 }
          where (ros, modulo) = calculateRootOfTrust nm by
                nm = intercalate "." nms

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [Proof] -> KD Proof
lemma nm f by = do cfg <- getKDConfig
                   lemmaWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
lemmaWith cfg nm = lemmaGen cfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proof] -> KD Proof
theorem nm f by = do cfg <- getKDConfig
                     theoremWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
theoremWith cfg nm = lemmaGen cfg "Theorem" [nm]

-- | Capture the general flow after a checkSat. We run the sat case if model is empty.
-- NB. This is the only place in Knuckledragger where we actually call check-sat;
-- so all interaction goes through here.
checkSatThen :: (SolverContext m, MonadIO m, MonadQuery m, Proposition a)
   => Bool               -- ^ verbose
   -> String             -- ^ tag
   -> SBool              -- ^ context
   -> a                  -- ^ what we want to prove
   -> [String]           -- ^ sub-proof
   -> Maybe (m r)        -- ^ special code to run if model is empty (if any)
   -> (Int -> IO r)      -- ^ what to do when unsat, with the tab amount
   -> m r
checkSatThen verbose tag ctx prop nms mbSat unsat = do
        inNewAssertionStack $ do
           tab <- liftIO $ startKD verbose tag nms
           constrain ctx

           -- Remember: We first have to negate, then skolemize
           constrain $ quantifiedBool $ skolemize (qNot prop)
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

-- | Given a predicate, return an induction principle for it. Typically, we only have one viable
-- induction principle for a given type, but we allow for alternative ones.
class InductionTactic a where
  -- | Induction tactic
  induct     :: a -> Proof

  -- | Alternative induction tactic
  inductAlt1 :: a -> Proof

  -- | Another alternative induction tactic
  inductAlt2 :: a -> Proof

  -- The second and third principles are the same as first by default, unless we provide them explicitly.
  inductAlt1 = induct
  inductAlt2 = induct

-- | Induction over SInteger. We provide various induction principles here: The first one
-- is over naturals, will only prove predicates that explicitly restrict the argument to >= 0.
-- The second and third ones are induction over the entire range of integers, two different
-- principles that might work better for different problems.
instance InductionTactic (SInteger -> SBool) where

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
instance SymVal a => InductionTactic (SBV a -> SInteger -> SBool) where
  induct p = internalAxiom "Nat.induct2" principle
     where qb a = quantifiedBool a

           principle =          qb (\(Forall a) -> p a 0)
                            .&& qb (\(Forall a) (Forall n) -> (n .>= 0 .&& p a n) .=> p a (n+1))
                     .=> qb --------------------------------------------------------------------
                                (\(Forall a) (Forall n) -> n .>= 0 .=> p a n)

-- | Induction over three argument predicates, with last argument SInteger.
instance (SymVal a, SymVal b) => InductionTactic (SBV a -> SBV b -> SInteger -> SBool) where
  induct p = internalAxiom "Nat.induct3" principle
     where qb a = quantifiedBool a

           principle =          qb (\(Forall a) (Forall b) -> p a b 0)
                            .&& qb (\(Forall a) (Forall b) (Forall n) -> (n .>= 0 .&& p a b n) .=> p a b (n+1))
                     .=> qb -----------------------------------------------------------------------------------
                                (\(Forall a) (Forall b) (Forall n) -> n .>= 0 .=> p a b n)

-- | Induction over four argument predicates, with last argument SInteger.
instance (SymVal a, SymVal b, SymVal c) => InductionTactic (SBV a -> SBV b -> SBV c -> SInteger -> SBool) where
  induct p = internalAxiom "Nat.induct4" principle
     where qb a = quantifiedBool a

           principle =          qb (\(Forall a) (Forall b) (Forall c) -> p a b c 0)
                            .&& qb (\(Forall a) (Forall b) (Forall c) (Forall n) -> (n .>= 0 .&& p a b c n) .=> p a b c (n+1))
                     .=> qb --------------------------------------------------------------------------------------------------
                                (\(Forall a) (Forall b) (Forall c) (Forall n) -> n .>= 0 .=> p a b c n)


-- | Induction over lists
instance SymVal a => InductionTactic (SList a -> SBool) where
  induct p = internalAxiom "List(a).induct" principle
    where qb a = quantifiedBool a

          principle =          p SL.nil
                           .&& qb (\(Forall x) (Forall xs) -> p xs .=> p (x SL..: xs))
                    .=> qb -----------------------------------------------------------
                               (\(Forall xs) -> p xs)

-- | Induction over two argument predicates, with last argument a list.
instance (SymVal a, SymVal e) => InductionTactic (SBV a -> SList e -> SBool) where
  induct p = internalAxiom "List(a).induct2" principle
    where qb a = quantifiedBool a

          principle =          qb (\(Forall a) -> p a SL.nil)
                           .&& qb (\(Forall a) (Forall e) (Forall es) -> p a es .=> p a (e SL..: es))
                    .=> qb --------------------------------------------------------------------------
                               (\(Forall a) (Forall es) -> p a es)

-- | Induction over three argument predicates, with last argument a list.
instance (SymVal a, SymVal b, SymVal e) => InductionTactic (SBV a -> SBV b -> SList e -> SBool) where
  induct p = internalAxiom "List(a).induct3" principle
    where qb a = quantifiedBool a

          principle =          qb (\(Forall a) (Forall b) -> p a b SL.nil)
                           .&& qb (\(Forall a) (Forall b) (Forall e) (Forall es) -> p a b es .=> p a b (e SL..: es))
                    .=> qb -----------------------------------------------------------------------------------------
                               (\(Forall a) (Forall b) (Forall xs) -> p a b xs)

-- | Induction over four argument predicates, with last argument a list.
instance (SymVal a, SymVal b, SymVal c, SymVal e) => InductionTactic (SBV a -> SBV b -> SBV c -> SList e -> SBool) where
  induct p = internalAxiom "List(a).induct4" principle
    where qb a = quantifiedBool a

          principle =          qb (\(Forall a) (Forall b) (Forall c) -> p a b c SL.nil)
                           .&& qb (\(Forall a) (Forall b) (Forall c) (Forall e) (Forall es) -> p a b c es .=> p a b c (e SL..: es))
                    .=> qb --------------------------------------------------------------------------------------------------------
                               (\(Forall a) (Forall b) (Forall c) (Forall xs) -> p a b c xs)

{- HLint ignore module "Eta reduce" -}
