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

{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KDKernel (
         Proposition,  Proven
       , axiom
       , lemma,        lemmaWith,   lemmaGen
       , theorem,      theoremWith
       , Induction(..)
       , sorry
       ) where

import Data.List (intercalate)

import Data.SBV
import Data.SBV.Core.Data (Constraint)

import qualified Data.SBV.List as SL

-- | A proposition is something SBV is capable of proving/disproving. We capture this
-- with a set of constraints. This type might look scary, but for the most part you
-- can ignore it and treat it as anything you can pass to 'prove' or 'sat' in SBV.
type Proposition a = ( QuantifiedBool a
                     , QNot a
                     , Satisfiable (SkolemsTo (NegatesTo a))
                     , Constraint Symbolic (SkolemsTo (NegatesTo a))
                     , Skolemize (NegatesTo a)
                     )

-- | Start a proof. We return the number of characters we printed, so the finisher can align the result.
start :: Bool -> String -> [String] -> IO Int
start newLine what nms = do putStr $ line ++ if newLine then "\n" else ""
                            return (length line)
  where tab    = 2 * length (drop 1 nms)
        indent = replicate tab ' '
        tag    = what ++ ": " ++ intercalate "." nms
        line   = indent ++ tag

-- | Finish a proof. First argument is what we got from the call of 'start' above.
finish :: String -> Int -> IO ()
finish what skip = putStrLn $ replicate (ribbonLength - skip) ' ' ++ what
  where -- Ideally an aestheticly pleasing length of the line. Perhaps this
        -- should be configurable, but this is good enough for now.
        ribbonLength :: Int
        ribbonLength = 50

-- | Keeping track of provenance information.
data Provenance = FromSorry String   -- ^ From a call to 'sorry'
                | FromAxiom String   -- ^ Created from an axiom/definition
                | FromLemma String   -- ^ Proven legitimately using the underlying solver

-- | A proven property. This type is left abstract, i.e., the only way to create on is via a
-- call to 'lemma'/'theorem' etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and KnuckleDragger kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
data Proven = Proven { provenance :: [Provenance] -- ^ What was used to establish
                     , getProof :: SBool          -- ^ Get the underlying boolean
                     }

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols. Note that we perform no checks on these propositions,
-- if you assert nonsense, then you get nonsense back. So, calls to 'axiom' should be limited to
-- definitions, or basic axioms (like commutativity, associativity) of uninterpreted function symbols.
axiom :: Proposition a => String -> a -> IO Proven
axiom nm p = do start False "Axiom" [nm] >>= finish "Admitted."
                pure Proven{ provenance = [FromAxiom nm]
                           , getProof   = quantifiedBool p
                           }

-- | Blindly believe a proposition as a theorem. This is in essence the same as 'axiom', except
-- it serves for documentation purposes that it should be provable. It's useful during development,
-- and also when you hit a theorem that the underlying solver just can't handle.
-- giving meaning to uninterpreted symbols. The list argument is unused, but it makes the
-- signature similar to 'lemma', allowing replacing `lemma` and `sorry` easily during development process.
sorry :: Proposition a => String -> a -> [b] -> IO Proven
sorry nm p _u = do start False "Sorry" [nm] >>= finish "Blindly believed."
                   pure Proven{ provenance = [FromSorry nm]
                              , getProof   = quantifiedBool p
                              }

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> [String] -> a -> [Proven] -> IO Proven
lemmaGen cfg what nms p by = do
    tab <- start (verbose cfg) what nms

    let nm = intercalate "." nms

        proposition = quantifiedBool (sAnd (map getProof by) .=> quantifiedBool p)

        good = do finish "Q.E.D." tab
                  pure Proven{ provenance = concatMap provenance by ++ [FromLemma nm]
                             , getProof   = quantifiedBool p
                             }

        cex  = do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                  -- Calculate as a sat call on negation, but print as a theorem
                  -- This allows for much better display of results.
                  SatResult res <- satWith cfg (skolemize (qNot p))
                  print $ ThmResult res
                  error "Failed"

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
lemma nm = lemmaGen defaultSMTCfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
lemmaWith cfg nm = lemmaGen cfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proven] -> IO Proven
theorem nm = lemmaGen defaultSMTCfg "Theorem" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
theoremWith cfg nm = lemmaGen cfg "Theorem" [nm]

-- | Given a predicate, return an induction principle for it. Typically, we only have one viable
-- induction principle for a given type, but we allow for alternative ones.
class Induction a where
  inductionPrinciple  :: (a -> SBool) -> IO Proven
  inductionPrinciple2 :: (a -> SBool) -> IO Proven
  inductionPrinciple3 :: (a -> SBool) -> IO Proven

  -- The second and third principles are the same as first by default, unless we provide them
  -- explicitly.
  inductionPrinciple2 = inductionPrinciple
  inductionPrinciple3 = inductionPrinciple

-- | Induction over SInteger. We provide various induction principles here: The first one
-- is over naturals, will only prove predicates that explicitly restrict the argument to >= 0.
-- The second and third ones are induction over the entire range of integers, two different
-- principles that might work better for different problems.
instance Induction SInteger where

   -- | Induction over naturals. Will prove predicates of the form @\n -> n >= 0 .=> predicate n@.
   inductionPrinciple p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                    .=> qb -----------------------------------------------------------
                                      (\(Forall n) -> n .>= 0 .=> p n)

      axiom "Nat.induction" principle

   -- | Induction over integers, using the strategy that @P(n)@ is equivalent to @P(n+1)@
   -- (i.e., not just @P(n) => P(n+1)@), thus covering the entire range.
   inductionPrinciple2 p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall i) -> p i .== p (i+1))
                    .=> qb ---------------------------------------------
                                    (\(Forall i) -> p i)

      axiom "Integer.induction" principle

   -- | Induction over integers, using the strategy that @P(n) => P(n+1)@ and @P(n) => P(n-1)@.
   inductionPrinciple3 p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall i) -> p i .=> p (i+1) .&& p (i-1))
                    .=> qb ---------------------------------------------------------
                                           (\(Forall i) -> p i)

      axiom "Integer.splitInduction" principle

-- | Induction over lists
instance SymVal a => Induction (SList a) where
  inductionPrinciple p = do
     let qb a = quantifiedBool a

         principle =       p SL.nil .&& qb (\(Forall x) (Forall xs) -> p xs .=> p (x SL..: xs))
                   .=> qb ----------------------------------------------------------------------
                                             (\(Forall xs) -> p xs)

     axiom "List(a).induction" principle
