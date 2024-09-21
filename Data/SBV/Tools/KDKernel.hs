-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KDKernel
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

module Data.SBV.Tools.KDKernel (
         Proposition,  Proof
       , axiom
       , lemma,        lemmaWith,   lemmaGen
       , theorem,      theoremWith
       , Induction(..)
       , sorry
       ) where

import Control.Monad.Trans  (liftIO)
import Control.Monad.Reader (ask)

import Data.List (intercalate, sort, nub)

import Data.SBV
import Data.SBV.Core.Data (Constraint)
import Data.SBV.Tools.KDUtils

import qualified Data.SBV.List as SL

-- | A proposition is something SBV is capable of proving/disproving. We capture this
-- with a set of constraints. This type might look scary, but for the most part you
-- can ignore it and treat it as anything you can pass to 'prove' or 'sat' in SBV.
type Proposition a = ( QuantifiedBool a
                     , QNot a
                     , Skolemize (NegatesTo a)
                     , Satisfiable (Symbolic (SkolemsTo (NegatesTo a)))
                     , Constraint  Symbolic  (SkolemsTo (NegatesTo a))
                     )

-- | Keeping track of where the sorry originates from. Used in displaying dependencies.
data RootOfTrust = None        -- ^ Trusts nothing (aside from SBV, underlying solver etc.)
                 | Self        -- ^ Trusts itself, i.e., established by a call to sorry
                 | Prop String -- ^ Trusts a parent that itself trusts something else. Note the name here is the
                               --   name of the proposition itself, not the parent that's trusted.

-- | Proof for a property. This type is left abstract, i.e., the only way to create on is via a
-- call to 'lemma'/'theorem' etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and KnuckleDragger kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
data Proof = Proof { rootOfTrust :: RootOfTrust -- ^ Root of trust, described above.
                   , isUserAxiom :: Bool        -- ^ Was this an axiom given by the user?
                   , getProof    :: SBool       -- ^ Get the underlying boolean
                   , proofName   :: String      -- ^ User given name
                   }

-- | Show instance for 'Proof'
instance Show Proof where
  show Proof{rootOfTrust, isUserAxiom, proofName} = '(' : tag ++ ") " ++ proofName
     where tag | isUserAxiom = "Axiom"
               | True        = case rootOfTrust of
                                 None   -> "Proven"
                                 Self   -> "Sorry"
                                 Prop s -> "Modulo: " ++ s

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols. Note that we perform no checks on these propositions,
-- if you assert nonsense, then you get nonsense back. So, calls to 'axiom' should be limited to
-- definitions, or basic axioms (like commutativity, associativity) of uninterpreted function symbols.
axiom :: Proposition a => String -> a -> KD Proof
axiom nm p = do start False "Axiom" [nm] >>= finish "Axiom."

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
lemmaGen :: Proposition a => KDConfig -> String -> [String] -> a -> [Proof] -> KD Proof
lemmaGen cfg what nms inputProp by = do
    tab <- start (kdVerbose cfg) what nms

    let underlyingSolver = kdSolverConfig cfg
        solver           = underlyingSolver{ verbose   = verbose   underlyingSolver || kdVerbose cfg
                                           , extraArgs = extraArgs underlyingSolver ++ kdExtraSolverArgs cfg
                                           }

        nm = intercalate "." nms

        -- What to do if all goes well
        good = do finish ("Q.E.D." ++ modulo) tab
                  pure Proof { rootOfTrust = ros
                             , isUserAxiom = False
                             , getProof    = label nm (quantifiedBool inputProp)
                             , proofName   = nm
                             }

          where parentRoots = map rootOfTrust by
                hasSelf     = not $ null [() | Self <- parentRoots]
                depNames    = nub $ sort [p | Prop p <- parentRoots]

                -- What's the root-of-trust for this node?
                -- If there are no "sorry" parents, and no parent nodes
                -- that are marked with a root of trust, then we don't have it either.
                -- Otherwise, mark it accordingly.
                (ros, modulo)
                   | not hasSelf && null depNames = (None,    "")
                   | True                         = (Prop nm, " [Modulo: " ++ why ++ "]")
                   where why | hasSelf = "sorry"
                             | True    = intercalate ", " depNames

        -- What to do if the proof fails
        cex  = liftIO $ do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."

                           -- When trying to get a counter-example, only include in the
                           -- implication those facts that are user-given axioms. This
                           -- way our counter-example will be more likely to be relevant
                           -- to the proposition we're currently proving. (Hopefully.)
                           -- Remember that we first have to negate, and then skolemize!
                           SatResult res <- satWith solver $ do
                                               mapM_ constrain [getProof | Proof{isUserAxiom, getProof} <- by, isUserAxiom] :: Symbolic ()
                                               pure $ skolemize (qNot inputProp)

                           print $ ThmResult res
                           error "Failed"

        -- bailing out
        failed r = liftIO $ do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                               print r
                               error "Failed"

    pRes <- liftIO $ proveWith solver $ do
                mapM_ (constrain . getProof) by :: Symbolic ()
                pure $ skolemize (quantifiedBool inputProp)

    case pRes of
      ThmResult Unsatisfiable{} -> good
      ThmResult Satisfiable{}   -> cex
      ThmResult DeltaSat{}      -> cex
      ThmResult SatExtField{}   -> cex
      ThmResult Unknown{}       -> failed pRes
      ThmResult ProofError{}    -> failed pRes

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [Proof] -> KD Proof
lemma nm f by = do cfg <- ask
                   lemmaWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => KDConfig -> String -> a -> [Proof] -> KD Proof
lemmaWith cfg nm = lemmaGen cfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proof] -> KD Proof
theorem nm f by = do cfg <- ask
                     theoremWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => KDConfig -> String -> a -> [Proof] -> KD Proof
theoremWith cfg nm = lemmaGen cfg "Theorem" [nm]

-- | Given a predicate, return an induction principle for it. Typically, we only have one viable
-- induction principle for a given type, but we allow for alternative ones.
class Induction a where
  induct     :: (a -> SBool) -> Proof
  inductAlt1 :: (a -> SBool) -> Proof
  inductAlt2 :: (a -> SBool) -> Proof

  -- The second and third principles are the same as first by default, unless we provide them explicitly.
  inductAlt1 = induct
  inductAlt2 = induct

  -- Induction for multiple argument predicates, inducting over the first argument
  induct2 :: SymVal b                       => (a -> SBV b ->                   SBool) -> Proof
  induct3 :: (SymVal b, SymVal c)           => (a -> SBV b -> SBV c ->          SBool) -> Proof
  induct4 :: (SymVal b, SymVal c, SymVal d) => (a -> SBV b -> SBV c -> SBV d -> SBool) -> Proof

-- | Induction over SInteger. We provide various induction principles here: The first one
-- is over naturals, will only prove predicates that explicitly restrict the argument to >= 0.
-- The second and third ones are induction over the entire range of integers, two different
-- principles that might work better for different problems.
instance Induction SInteger where

   -- | Induction over naturals. Will prove predicates of the form @\n -> n >= 0 .=> predicate n@.
   induct p = internalAxiom "Nat.induct" principle
      where qb = quantifiedBool

            principle =       p 0 .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                      .=> qb -----------------------------------------------------------
                                        (\(Forall n) -> n .>= 0 .=> p n)


   -- | Induction over integers, using the strategy that @P(n)@ is equivalent to @P(n+1)@
   -- (i.e., not just @P(n) => P(n+1)@), thus covering the entire range.
   inductAlt1 p = internalAxiom "Integer.inductAlt1" principle
     where qb = quantifiedBool

           principle =           p 0
                             .&& qb (\(Forall i) -> p i .== p (i+1))
                     .=> qb -----------------------------------------
                                 (\(Forall i) -> p i)

   -- | Induction over integers, using the strategy that @P(n) => P(n+1)@ and @P(n) => P(n-1)@.
   inductAlt2 p = internalAxiom "Integer.inductAlt2" principle
     where qb = quantifiedBool

           principle =           p 0
                             .&& qb (\(Forall i) -> p i .=> p (i+1) .&& p (i-1))
                     .=> qb -----------------------------------------------------
                                 (\(Forall i) -> p i)

   induct2 p = internalAxiom "Nat.induct2" principle
      where qb a = quantifiedBool a

            principle =           qb (\(Forall a) -> p 0 a)
                              .&& qb (\(Forall n) (Forall a) -> (n .>= 0 .&& p n a) .=> p (n+1) a)
                      .=> qb ----------------------------------------------------------------------
                                  (\(Forall n) (Forall a) -> n .>= 0 .=> p n a)

   induct3 p = internalAxiom "Nat.induct3" principle
      where qb a = quantifiedBool a

            principle =           qb (\(Forall a) (Forall b) -> p 0 a b)
                              .&& qb (\(Forall n) (Forall a) (Forall b) -> (n .>= 0 .&& p n a b) .=> p (n+1) a b)
                      .=> qb -------------------------------------------------------------------------------------
                                  (\(Forall n) (Forall a) (Forall b) -> n .>= 0 .=> p n a b)

   induct4 p = internalAxiom "Nat.induct4" principle
      where qb a = quantifiedBool a

            principle =           qb (\(Forall a) (Forall b) (Forall c) -> p 0 a b c)
                              .&& qb (\(Forall n) (Forall a) (Forall b) (Forall c) -> (n .>= 0 .&& p n a b c) .=> p (n+1) a b c)
                      .=> qb ----------------------------------------------------------------------------------------------------
                                  (\(Forall n) (Forall a) (Forall b) (Forall c) -> n .>= 0 .=> p n a b c)


-- | Induction over lists
instance SymVal a => Induction (SList a) where
  induct p = internalAxiom "List(a).induct1" principle
    where qb a = quantifiedBool a

          principle =           p SL.nil
                            .&& qb (\(Forall x) (Forall xs) -> p xs .=> p (x SL..: xs))
                    .=> qb -------------------------------------------------------------
                                (\(Forall xs) -> p xs)

  induct2 p = internalAxiom "List(a).induct2" principle
    where qb a = quantifiedBool a

          principle =           qb (\(Forall a) -> p SL.nil a)
                            .&& qb (\(Forall x) (Forall xs) (Forall a) -> p xs a .=> p (x SL..: xs) a)
                    .=> qb ----------------------------------------------------------------------------
                                (\(Forall xs) (Forall a) -> p xs a)

  induct3 p = internalAxiom "List(a).induct3" principle
    where qb a = quantifiedBool a

          principle =           qb (\(Forall a) (Forall b) -> p SL.nil a b)
                            .&& qb (\(Forall x) (Forall xs) (Forall a) (Forall b) -> p xs a b .=> p (x SL..: xs) a b)
                    .=> qb -------------------------------------------------------------------------------------------
                                (\(Forall xs) (Forall a) (Forall b) -> p xs a b)

  induct4 p = internalAxiom "List(a).induct4" principle
    where qb a = quantifiedBool a

          principle =           qb (\(Forall a) (Forall b) (Forall c) -> p SL.nil a b c)
                            .&& qb (\(Forall x) (Forall xs) (Forall a) (Forall b) (Forall c) -> p xs a b c .=> p (x SL..: xs) a b c)
                    .=> qb ----------------------------------------------------------------------------------------------------------
                                (\(Forall xs) (Forall a) (Forall b) (Forall c) -> p xs a b c)

{- HLint ignore module "Eta reduce" -}
