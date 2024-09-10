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
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KDKernel (
         Proposition,  Proven
       , axiom
       , lemma,        lemmaWith,   lemmaGen
       , theorem,      theoremWith
       , Induction(..)
       , sorry
       ) where

import Data.List (intercalate, sort, nub)

import System.IO (hFlush, stdout)

import Data.SBV
import Data.SBV.Core.Data (Constraint)

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

-- | A proven property. This type is left abstract, i.e., the only way to create on is via a
-- call to 'lemma'/'theorem' etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and KnuckleDragger kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
data Proven = Proven { rootOfTrust :: RootOfTrust -- ^ Root of trust, described above.
                     , isUserAxiom :: Bool        -- ^ Was this an axiom given by the user?
                     , getProof    :: SBool       -- ^ Get the underlying boolean
                     }

-- | Start a proof. We return the number of characters we printed, so the finisher can align the result.
start :: Bool -> String -> [String] -> IO Int
start newLine what nms = do putStr $ line ++ if newLine then "\n" else ""
                            hFlush stdout
                            return (length line)
  where tab    = 2 * length (drop 1 nms)
        indent = replicate tab ' '
        tag    = what ++ ": " ++ intercalate "." nms
        line   = indent ++ tag

-- | Finish a proof. First argument is what we got from the call of 'start' above.
finish :: String -> Int -> IO ()
finish what skip = do putStrLn $ replicate (ribbonLength - skip) ' ' ++ what
  where -- Ideally an aestheticly pleasing length of the line. Perhaps this
        -- should be configurable, but this is good enough for now.
        ribbonLength :: Int
        ribbonLength = 40

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols. Note that we perform no checks on these propositions,
-- if you assert nonsense, then you get nonsense back. So, calls to 'axiom' should be limited to
-- definitions, or basic axioms (like commutativity, associativity) of uninterpreted function symbols.
axiom :: Proposition a => String -> a -> IO Proven
axiom nm p = do start False "Axiom" [nm] >>= finish "Axiom."

                pure (internalAxiom nm p) { isUserAxiom = True }

-- | Internal axiom generator; so we can keep truck of KnuckleDrugger's trusted axioms, vs. user given axioms.
-- Not exported.
internalAxiom :: Proposition a => String -> a -> Proven
internalAxiom nm p = Proven { rootOfTrust = None
                            , isUserAxiom = False
                            , getProof    = label nm (quantifiedBool p)
                            }

-- | A manifestly false theorem. This is useful when we want to prove a theorem that the underlying solver
-- cannot deal with, or if we want to postpone the proof for the time being. KnuckleDragger will keep
-- track of the uses of 'sorry' and will print them appropriately while printing proofs.
sorry :: Proven
sorry = Proven{ rootOfTrust = Self
              , isUserAxiom = False
              , getProof    = label "SORRY" (quantifiedBool p)
              }
  where -- ideally, I'd rather just use 
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall (x :: SBool)) = label "SORRY: KnuckleDragger, proof uses \"sorry\"" x

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> [String] -> a -> [Proven] -> IO Proven
lemmaGen cfg what nms inputProp by = do
    tab <- start (verbose cfg) what nms

    let nm = intercalate "." nms

        proposition = quantifiedBool (sAnd (map getProof by) .=> quantifiedBool inputProp)

        -- What to do if all goes well
        good = do finish ("Q.E.D." ++ modulo) tab
                  pure Proven { rootOfTrust = ros
                              , isUserAxiom = False
                              , getProof    = label nm (quantifiedBool inputProp)
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
        cex  = do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                  -- When trying to get a counter-example, only include in the
                  -- implication those facts that are user-given axioms. This
                  -- way our counter-example will be more likely to be relevant
                  -- to the proposition we're currently proving. (Hopefully.)
                  -- Remember that we first have to negate, and then skolemize!
                  SatResult res <- satWith cfg $ do
                                      mapM_ constrain [getProof | Proven{isUserAxiom, getProof} <- by, isUserAxiom] :: Symbolic ()
                                      pure $ skolemize (qNot inputProp)
                  print $ ThmResult res
                  error "Failed"

        -- bailing out
        failed r = do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                      print r
                      error "Failed"

    pRes <- proveWith cfg proposition
    case pRes of
      ThmResult Unsatisfiable{} -> good
      ThmResult Satisfiable{}   -> cex
      ThmResult DeltaSat{}      -> cex
      ThmResult SatExtField{}   -> cex
      ThmResult Unknown{}       -> failed pRes
      ThmResult ProofError{}    -> failed pRes

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [Proven] -> IO Proven
lemma = lemmaWith defaultSMTCfg

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
lemmaWith cfg nm = lemmaGen cfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proven] -> IO Proven
theorem = theoremWith defaultSMTCfg

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
theoremWith cfg nm = lemmaGen cfg "Theorem" [nm]

-- | Given a predicate, return an induction principle for it. Typically, we only have one viable
-- induction principle for a given type, but we allow for alternative ones.
class Induction a where
  induct     :: (a -> SBool) -> Proven
  inductAlt1 :: (a -> SBool) -> Proven
  inductAlt2 :: (a -> SBool) -> Proven

  -- The second and third principles are the same as first by default, unless we provide them explicitly.
  inductAlt1 = induct
  inductAlt2 = induct

  -- Induction for multiple argument predicates, inducting over the first argument
  induct2 :: SymVal b                       => (a -> SBV b ->                   SBool) -> Proven
  induct3 :: (SymVal b, SymVal c)           => (a -> SBV b -> SBV c ->          SBool) -> Proven
  induct4 :: (SymVal b, SymVal c, SymVal d) => (a -> SBV b -> SBV c -> SBV d -> SBool) -> Proven

  induct2 f = induct $ \a -> quantifiedBool (\(Forall b)                       -> f a b)
  induct3 f = induct $ \a -> quantifiedBool (\(Forall b) (Forall c)            -> f a b c)
  induct4 f = induct $ \a -> quantifiedBool (\(Forall b) (Forall c) (Forall d) -> f a b c d)

-- | Induction over SInteger. We provide various induction principles here: The first one
-- is over naturals, will only prove predicates that explicitly restrict the argument to >= 0.
-- The second and third ones are induction over the entire range of integers, two different
-- principles that might work better for different problems.
instance Induction SInteger where

   -- | Induction over naturals. Will prove predicates of the form @\n -> n >= 0 .=> predicate n@.
   induct p = internalAxiom "Nat.induction" principle
      where qb = quantifiedBool

            principle =       p 0 .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                      .=> qb -----------------------------------------------------------
                                        (\(Forall n) -> n .>= 0 .=> p n)


   -- | Induction over integers, using the strategy that @P(n)@ is equivalent to @P(n+1)@
   -- (i.e., not just @P(n) => P(n+1)@), thus covering the entire range.
   inductAlt1 p = internalAxiom "Integer.induction" principle
     where qb = quantifiedBool

           principle =       p 0 .&& qb (\(Forall i) -> p i .== p (i+1))
                     .=> qb ---------------------------------------------
                                     (\(Forall i) -> p i)

   -- | Induction over integers, using the strategy that @P(n) => P(n+1)@ and @P(n) => P(n-1)@.
   inductAlt2 p = internalAxiom "Integer.splitInduction" principle
     where qb = quantifiedBool

           principle =       p 0 .&& qb (\(Forall i) -> p i .=> p (i+1) .&& p (i-1))
                     .=> qb ---------------------------------------------------------
                                             (\(Forall i) -> p i)

-- | Induction over lists
instance SymVal a => Induction (SList a) where
  induct p = internalAxiom "List(a).induction" principle
    where qb a = quantifiedBool a

          principle =       p SL.nil .&& qb (\(Forall x) (Forall xs) -> p xs .=> p (x SL..: xs))
                    .=> qb ----------------------------------------------------------------------
                                              (\(Forall xs) -> p xs)
