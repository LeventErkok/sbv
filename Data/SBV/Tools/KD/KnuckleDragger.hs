-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KD.KnuckleDragger
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
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KD.KnuckleDragger (
         Proposition, Proof, Instantiatable(..), Inst(..)
       , axiom
       , lemma,        lemmaWith
       , theorem,      theoremWith
       , calcLemma,   calcLemmaWith
       , calcTheorem, calcTheoremWith
       , induct, inductAlt1, inductAlt2
       , inductiveLemma,   inductiveLemmaWith
       , inductiveTheorem, inductiveTheoremWith
       , sorry
       , KD, runKD, runKDWith, use
       , (|-), (=:), (?), qed
       ) where

import Data.SBV
import Data.SBV.Core.Model (qSaturateSavingObservables)

import Data.SBV.Control hiding (getProof)

import Data.SBV.Tools.KD.Kernel
import Data.SBV.Tools.KD.Utils

import Control.Monad.Trans (liftIO)

import qualified Data.SBV.List as SL

import Data.Char (isSpace)
import Data.List (isPrefixOf, isSuffixOf)
import Data.Maybe (catMaybes)

import Data.Proxy
import GHC.TypeLits (KnownSymbol, symbolVal, Symbol)

import Data.SBV.Utils.TDiff

import Data.Dynamic

-- | Bring an IO proof into current proof context.
use :: IO Proof -> KD Proof
use = liftIO

-- | A class for doing equational reasoning style calculational proofs. Use 'calcLemma' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class CalcLemma a steps where

  -- | Prove a property via a series of equality steps, using the default solver.
  -- Let @H@ be a list of already established lemmas. Let @P@ be a property we wanted to prove, named @name@.
  -- Consider a call of the form @calcLemma name P (cond, [A, B, C, D]) H@. Note that @H@ is
  -- a list of already proven facts, ensured by the type signature. We proceed as follows:
  --
  --    * Prove: @(H && cond)                                   -> (A == B)@
  --    * Prove: @(H && cond && A == B)                         -> (B == C)@
  --    * Prove: @(H && cond && A == B && B == C)               -> (C == D)@
  --    * Prove: @(H && (cond -> (A == B && B == C && C == D))) -> P@
  --    * If all of the above steps succeed, conclude @P@.
  --
  -- cond acts as the context. Typically, if you are trying to prove @Y -> Z@, then you want cond to be Y.
  -- (This is similar to @intros@ commands in theorem provers.)
  --
  -- So, calc-lemma is essentially modus-ponens, applied in a sequence of stepwise equality reasoning in the case of
  -- non-boolean steps.
  --
  -- If there are no helpers given (i.e., if @H@ is empty), then this call is equivalent to 'lemmaWith'.
  -- If @H@ is a singleton, then we bail out. A single step in @H@ indicates a usage mistake, since there's
  -- no sequence of steps to reason about.
  calcLemma :: Proposition a => String -> a -> steps -> KD Proof

  -- | Same as calcLemma, except tagged as Theorem
  calcTheorem :: Proposition a => String -> a -> steps -> KD Proof

  -- | Prove a property via a series of equality steps, using the given solver.
  calcLemmaWith :: Proposition a => SMTConfig -> String -> a -> steps -> KD Proof

  -- | Same as calcLemmaWith, except tagged as Theorem
  calcTheoremWith :: Proposition a => SMTConfig -> String -> a -> steps -> KD Proof

  -- | Internal, shouldn't be needed outside the library
  {-# MINIMAL calcSteps #-}
  calcSteps :: a -> steps -> Symbolic (SBool, (SBool, [([Proof], SBool)]))

  calcLemma   nm p steps = getKDConfig >>= \cfg -> calcLemmaWith   cfg nm p steps
  calcTheorem nm p steps = getKDConfig >>= \cfg -> calcTheoremWith cfg nm p steps
  calcLemmaWith          = calcGeneric False
  calcTheoremWith        = calcGeneric True

  calcGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> KD Proof
  calcGeneric tagTheorem cfg@SMTConfig{kdOptions = KDOptions{measureTime}} nm result steps = do
          kdSt <- getKDState

          liftIO $ runSMTWith cfg $ do

             qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

             message cfg $ "Chain " ++ (if tagTheorem then "theorem" else "lemma") ++ ": " ++ nm ++ "\n"

             mbStartTime <- getTimeStampIf measureTime

             (goal, (intros, proofSteps)) <- calcSteps result steps

             let stepHelpers   = concatMap fst proofSteps
                 (ros, modulo) = calculateRootOfTrust nm stepHelpers
                 finish        = finishKD cfg ("Q.E.D." ++ modulo)

             mapM_ (qSaturateSavingObservables . getProof) stepHelpers

             let go :: Int -> SBool -> [([Proof], SBool)] -> Query Proof
                 go _ accum [] = do
                     queryDebug [nm ++ ": Chain proof end: proving the result:"]
                     checkSatThen cfg kdSt "Result" True
                                  (Just (intros .=> accum))
                                  goal
                                  []
                                  ["", ""]
                                  (Just [nm, "Result"])
                                  Nothing $ \d -> do mbElapsed <- getElapsedTime mbStartTime
                                                     finish d $ catMaybes [mbElapsed]
                                                     pure Proof { rootOfTrust = ros
                                                                , isUserAxiom = False
                                                                , getProof    = label nm (quantifiedBool result)
                                                                , getProp     = toDyn result
                                                                , proofName   = nm
                                                                }

                 go i accum ((by, s):ss) = do
                      queryDebug [nm ++ ": Chain proof step: " ++ show i ++ " to " ++ show (i+1) ++ ":"]
                      checkSatThen cfg kdSt "Step  "
                                            True
                                            (Just (intros .&& accum .&& sAnd (map getProof by)))
                                            s
                                            []
                                            ["", show i]
                                            (Just [nm, show i])
                                            Nothing
                                            (flip finish [])

                      go (i+1) (s .&& accum) ss

             query $ go (1::Int) sTrue proofSteps

-- | Turn a sequence of steps into a chain of equalities
mkCalcSteps :: EqSymbolic a => (SBool, [ProofStep a]) -> (SBool, [([Proof], SBool)])
mkCalcSteps (intros, xs) = (intros, zipWith merge xs (drop 1 xs))
  where merge (ProofStep a by) (ProofStep b _) = (by, a .== b)

-- | Chaining lemmas that depend on a single quantified variable.
instance (KnownSymbol na, SymVal a, EqSymbolic z) => CalcLemma (Forall na a -> SBool) (SBV a -> (SBool, [ProofStep z])) where
   calcSteps result steps = do a <- free (symbolVal (Proxy @na))
                               pure (result (Forall a), mkCalcSteps (steps a))

-- | Chaining lemmas that depend on two quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> SBool)
                   (SBV a -> SBV b -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                               pure (result (Forall a) (Forall b), mkCalcSteps (steps a b))

-- | Chaining lemmas that depend on three quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> SBool)
                   (SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b, c) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                               pure (result (Forall a) (Forall b) (Forall c), mkCalcSteps (steps a b c))

-- | Chaining lemmas that depend on four quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                   (SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b, c, d) <- (,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d), mkCalcSteps (steps a b c d))

-- | Chaining lemmas that depend on five quantified variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool)
                   (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b, c, d, e) <- (,,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e), mkCalcSteps (steps a b c d e))

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

   inductiveLemma   nm p steps by = getKDConfig >>= \cfg -> inductiveLemmaWith   cfg nm p steps by
   inductiveTheorem nm p steps by = getKDConfig >>= \cfg -> inductiveTheoremWith cfg nm p steps by
   inductiveLemmaWith             = inductGeneric False
   inductiveTheoremWith           = inductGeneric True

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL inductionStrategy #-}
   inductionStrategy :: Proposition a => a -> steps -> Symbolic InductionStrategy

   inductGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof
   inductGeneric tagTheorem cfg@SMTConfig{kdOptions = KDOptions{measureTime}} nm result steps helpers = do

     kdSt <- getKDState

     liftIO $ do

        message cfg $ "Inductive " ++ (if tagTheorem then "theorem" else "lemma") ++ ": " ++ nm ++ "\n"

        mbStartTime <- getTimeStampIf measureTime

        runSMTWith cfg $ do

           qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

           mapM_ (constrain . getProof) helpers

           let (ros, modulo) = calculateRootOfTrust nm helpers
               finish et d  = finishKD cfg ("Q.E.D." ++ modulo) d et

           InductionStrategy { inductionBaseCase
                             , inductiveHypothesis
                             , inductionHelperSteps
                             , inductionBaseFailureMsg
                             , inductiveStep
                             } <- inductionStrategy result steps

           query $ do

            queryDebug [nm ++ ": Induction, proving base case:"]
            checkSatThen cfg kdSt "Base" True Nothing inductionBaseCase helpers [nm, "Base"] Nothing
                         (Just (liftIO (putStrLn inductionBaseFailureMsg)))
                         (finish [])

            constrain inductiveHypothesis

            let loop accum ((snm, s):ss) = do
                    queryDebug [nm ++ ": Induction, proving helper: " ++ snm]
                    checkSatThen cfg kdSt "Help" True (Just accum) s helpers [nm, snm] Nothing Nothing (finish [])
                    loop (accum .&& s) ss

                loop accum [] = pure accum

            -- Get the schema
            indSchema <- loop sTrue inductionHelperSteps

            -- Do the final proof:
            queryDebug [nm ++ ": Induction, proving inductive step:"]
            checkSatThen cfg kdSt "Step" True (Just indSchema) inductiveStep helpers [nm, "Step"] Nothing Nothing $ \d -> do
              mbElapsed <- getElapsedTime mbStartTime
              finish (catMaybes [mbElapsed]) d
              pure $ Proof { rootOfTrust = ros
                           , isUserAxiom = False
                           , getProof    = label nm $ quantifiedBool result
                           , getProp     = toDyn result
                           , proofName   = nm
                           }

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

-- | Induction over 'SInteger'.
instance   (KnownSymbol nk, EqSymbolic z)
        => Inductive (Forall nk Integer -> SBool)
                     (SInteger -> ([z], [z]))
 where
   inductionStrategy result steps = do
       let predicate k = result (Forall k)
           nk          = symbolVal (Proxy @nk)

       k <- free nk
       constrain $ k .>= 0

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
   inductionStrategy result steps = do
       let predicate a k = result (Forall a) (Forall k)
           na            = symbolVal (Proxy @na)
           nk            = symbolVal (Proxy @nk)

       a <- free na
       k <- free nk
       constrain $ k .>= 0

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
   inductionStrategy result steps = do
       let predicate a b k = result (Forall a) (Forall b) (Forall k)
           na              = symbolVal (Proxy @na)
           nb              = symbolVal (Proxy @nb)
           nk              = symbolVal (Proxy @nk)

       a <- free na
       b <- free nb
       k <- free nk
       constrain $ k .>= 0

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
   inductionStrategy result steps = do
       let predicate a b c k = result (Forall a) (Forall b) (Forall c) (Forall k)
           na                = symbolVal (Proxy @na)
           nb                = symbolVal (Proxy @nb)
           nc                = symbolVal (Proxy @nc)
           nk                = symbolVal (Proxy @nk)

       a <- free na
       b <- free nb
       c <- free nc
       k <- free nk
       constrain $ k .>= 0

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
   inductionStrategy result steps = do
       let predicate a b c d k = result (Forall a) (Forall b) (Forall c) (Forall d) (Forall k)
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
   inductionStrategy result steps = do
       let predicate k = result (Forall k)
           nks         = symbolVal (Proxy @nk)
           nk          = singular nks

       k  <- free nk
       ks <- free nks

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
   inductionStrategy result steps = do
       let predicate a k = result (Forall a) (Forall k)
           na            = symbolVal (Proxy @na)
           nks           = symbolVal (Proxy @nk)
           nk            = singular nks

       a  <- free na
       k  <- free nk
       ks <- free nks

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
   inductionStrategy result steps = do
       let predicate a b k = result (Forall a) (Forall b) (Forall k)
           na              = symbolVal (Proxy @na)
           nb              = symbolVal (Proxy @nb)
           nks             = symbolVal (Proxy @nk)
           nk              = singular nks

       a  <- free na
       b  <- free nb
       k  <- free nk
       ks <- free nks

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
   inductionStrategy result steps = do
       let predicate a b c k = result (Forall a) (Forall b) (Forall c) (Forall k)
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
   inductionStrategy result steps = do
       let predicate a b c d k = result (Forall a) (Forall b) (Forall c) (Forall d) (Forall k)
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

       pure InductionStrategy {
                inductionBaseCase       = predicate a b c d SL.nil
              , inductiveHypothesis     = predicate a b c d ks
              , inductionHelperSteps    = pairInductiveSteps (steps a b c d k ks)
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate a b c d (k SL..: ks))
              }

-- | Instantiation for a universally quantified variable
newtype Inst (nm :: Symbol) a = Inst (SBV a)

instance KnownSymbol nm => Show (Inst nm a) where
   show (Inst a) = symbolVal (Proxy @nm) ++ " |-> " ++ show a

-- | Instantiating a proof at different types of arguments. This is necessarily done using
-- dynamics, hand has a cost of not being applicable.
class Instantiatable a where
  -- | Apply a universal proof to some arguments, creating an instance of the proof itself.
  at :: Proof -> a -> Proof

-- | Single parameter
instance (KnownSymbol na, HasKind a, Typeable a) => Instantiatable (Inst na a) where
  at = instantiate $ \f (Inst a) -> f (Forall a :: Forall na a)

-- | Two parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         ) => Instantiatable (Inst na a, Inst nb b) where
  at = instantiate $ \f (Inst a, Inst b) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b)

-- | Three parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         ) => Instantiatable (Inst na a, Inst nb b, Inst nc c) where
  at = instantiate $ \f (Inst a, Inst b, Inst c) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c)

-- | Four parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         , KnownSymbol nd, HasKind d, Typeable d
         ) => Instantiatable (Inst na a, Inst nb b, Inst nc c, Inst nd d) where
  at = instantiate $ \f (Inst a, Inst b, Inst c, Inst d) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d)

-- | Five parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         , KnownSymbol nd, HasKind d, Typeable d
         , KnownSymbol ne, HasKind e, Typeable e
         ) => Instantiatable (Inst na a, Inst nb b, Inst nc c, Inst nd d, Inst ne e) where
  at = instantiate $ \f (Inst a, Inst b, Inst c, Inst d, Inst e) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d) (Forall e :: Forall ne e)

instantiate :: (Typeable f, Show arg) => (f -> arg -> SBool) -> Proof -> arg -> Proof
instantiate ap p@Proof{getProp, proofName} a = case fromDynamic getProp of
                                                 Nothing -> cantInstantiate
                                                 Just f  -> let result = f `ap` a
                                                                nm     = proofName ++ " @ " ++ paren sha
                                                            in p { getProof  = label nm result
                                                                 , getProp   = toDyn result
                                                                 , proofName = nm
                                                                 }
 where sha = show a
       cantInstantiate = error $ unlines [ "at: Cannot instantiate proof:"
                                         , "   Name: " ++ proofName
                                         , "   Type: " ++ trim (show getProp)
                                         , "   At  : " ++ sha
                                         ]

       -- dynamic puts funky <</>> at the beginning and end; trim it:
       trim  ('<':'<':s) = reverse (trimE (reverse s))
       trim  s           = s
       trimE ('>':'>':s) = s
       trimE s           = s

       -- Add parens if necessary
       paren s | "(" `isPrefixOf` s && ")" `isSuffixOf` s = s
               | all (not . isSpace) s                    = s
               | True                                     = '(' : s ++ ")"

-- | A proof-step with associated helpers
data ProofStep a = ProofStep a [Proof]

-- | Class capturing giving a proof-step helper
class ProofHint a b where
  -- | Specify a helper for the given proof step
  (?) :: a -> b -> ProofStep a
  infixl 2 ?

-- | Giving just one proof as a helper.
instance ProofHint a Proof where
  a ? p = ProofStep a [p]

-- | Giving a bunch of proofs as a helper.
instance ProofHint a [Proof] where
  a ? ps = ProofStep a ps

-- | Capture what a given step can chain-to. This is a closed-type family, i.e.,
-- we don't allow users to change this and write other chainable things. Probably it is not really necessary,
-- but we'll cross that bridge if someone actually asks for it.
type family ChainsTo a where
  ChainsTo (ProofStep a) = [ProofStep a]
  ChainsTo a             = [ProofStep a]

-- | Chain steps in a calculational proof.
(=:) :: ChainStep a (ChainsTo a) =>  a -> ChainsTo a -> ChainsTo a
(=:) = chain
infixr 1 =:

-- | Chaining two steps together
class ChainStep a b where
  chain :: a -> b -> b

-- | Chaining from a value without any annotation
instance ChainStep a [ProofStep a] where
  chain x y = ProofStep x [] : y

-- | Chaining from another proof step
instance ChainStep (ProofStep a) [ProofStep a] where
  chain x y = x : y

-- | Mark the end of a calculational proof.
qed :: [ProofStep a]
qed = []

-- | Start a calculational proof, with the given hypothesis. Use 'sTrue' as the
-- first argument if the calculation holds unconditionally. The first argument is
-- typically used to introduce hypotheses in proofs of implications such as @A .=> B@, where
-- we would put @A@ as the starting assumption.
(|-) :: SBool -> [ProofStep a] -> (SBool, [ProofStep a])
hyp |- ps = (hyp, ps)
infixl 0 |-
