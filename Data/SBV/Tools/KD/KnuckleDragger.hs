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
       , lemma,   lemmaWith
       , theorem, theoremWith
       , calc,   calcWith,   calcThm,   calcThmWith
       , induct, inductWith, inductThm, inductThmWith
       , sorry
       , KD, runKD, runKDWith, use
       , (|-), (⊢), (=:), (≡), (?), qed
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

-- | A class for doing equational reasoning style calculational proofs. Use 'calc' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class CalcLemma a steps where

  -- | Prove a property via a series of equality steps, using the default solver.
  -- Let @H@ be a list of already established lemmas. Let @P@ be a property we wanted to prove, named @name@.
  -- Consider a call of the form @calc name P (cond, [A, B, C, D]) H@. Note that @H@ is
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
  calc :: Proposition a => String -> a -> steps -> KD Proof

  -- | Same as calc, except tagged as Theorem
  calcThm :: Proposition a => String -> a -> steps -> KD Proof

  -- | Prove a property via a series of equality steps, using the given solver.
  calcWith :: Proposition a => SMTConfig -> String -> a -> steps -> KD Proof

  -- | Same as calcWith, except tagged as Theorem
  calcThmWith :: Proposition a => SMTConfig -> String -> a -> steps -> KD Proof

  -- | Internal, shouldn't be needed outside the library
  {-# MINIMAL calcSteps #-}
  calcSteps :: a -> steps -> Symbolic (SBool, (SBool, [([Proof], SBool)]))

  calc    nm p steps = getKDConfig >>= \cfg -> calcWith    cfg nm p steps
  calcThm nm p steps = getKDConfig >>= \cfg -> calcThmWith cfg nm p steps
  calcWith           = calcGeneric False
  calcThmWith        = calcGeneric True

  calcGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> KD Proof
  calcGeneric tagTheorem cfg@SMTConfig{kdOptions = KDOptions{measureTime}} nm result steps = do
     kdSt <- getKDState

     liftIO $ runSMTWith cfg $ do

        qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

        message cfg $ (if tagTheorem then "Theorem" else "Lemma") ++ ": " ++ nm ++ "\n"

        mbStartTime <- getTimeStampIf measureTime

        (goal, (calcIntros, proofSteps)) <- calcSteps result steps

        let stepHelpers   = concatMap fst proofSteps
            (ros, modulo) = calculateRootOfTrust nm stepHelpers
            finish        = finishKD cfg ("Q.E.D." ++ modulo)

        mapM_ (qSaturateSavingObservables . getProof) stepHelpers

        let go :: Int -> SBool -> [([Proof], SBool)] -> Query Proof
            go _ accum [] = do
                queryDebug [nm ++ ": Proof end: proving the result:"]
                checkSatThen cfg kdSt "Result" True
                             (Just (calcIntros .=> accum))
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
                 queryDebug [nm ++ ": Proof step: " ++ show i ++ " to " ++ show (i+1) ++ ":"]
                 checkSatThen cfg kdSt "Step  "
                                       True
                                       (Just (calcIntros .&& sAnd (map getProof by)))
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
data InductionStrategy = InductionStrategy { inductionIntros         :: SBool
                                           , inductionBaseCase       :: SBool
                                           , inductionProofSteps     :: [([Proof], SBool)]
                                           , inductionBaseFailureMsg :: String
                                           , inductiveStep           :: SBool
                                           }

-- | A class for doing inductive proofs, with the possibility of explicit steps.
class Inductive a steps where
   -- | Inductively prove a lemma, using the default config.
   induct :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Inductively prove a theorem. Same as 'inductiveLemma', but tagged as a theorem, using the default config.
   inductThm :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'inductiveLemma', but with the given solver configuration.
   inductWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'inductiveTheorem, but with the given solver configuration.
   inductThmWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   induct    nm p steps = getKDConfig >>= \cfg -> inductWith    cfg nm p steps
   inductThm nm p steps = getKDConfig >>= \cfg -> inductThmWith cfg nm p steps
   inductWith           = inductGeneric False
   inductThmWith        = inductGeneric True

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL inductionStrategy #-}
   inductionStrategy :: Proposition a => a -> (Proof -> steps) -> Symbolic InductionStrategy

   inductGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof
   inductGeneric tagTheorem cfg@SMTConfig{kdOptions = KDOptions{measureTime}} nm result steps = do
      kdSt <- getKDState

      liftIO $ runSMTWith cfg $ do

         qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

         message cfg $ "Inductive " ++ (if tagTheorem then "theorem" else "lemma") ++ ": " ++ nm ++ "\n"

         mbStartTime <- getTimeStampIf measureTime

         InductionStrategy { inductionIntros
                           , inductionBaseCase
                           , inductionProofSteps
                           , inductionBaseFailureMsg
                           , inductiveStep
                           } <- inductionStrategy result steps

         let stepHelpers   = concatMap fst inductionProofSteps
             (ros, modulo) = calculateRootOfTrust nm stepHelpers
             finish et d   = finishKD cfg ("Q.E.D." ++ modulo) d et

         mapM_ (qSaturateSavingObservables . getProof) stepHelpers

         query $ do

          queryDebug [nm ++ ": Induction, proving base case:"]
          checkSatThen cfg kdSt "Base" True (Just inductionIntros) inductionBaseCase [] [nm, "Base"] Nothing
                       (Just (liftIO (putStrLn inductionBaseFailureMsg)))
                       (finish [])

          let loop i accum ((by, s):ss) = do
                  queryDebug [nm ++ ": Induction, proving step: " ++ show i]
                  checkSatThen cfg kdSt "Step"
                                        True
                                        (Just (inductionIntros .&& sAnd (map getProof by)))
                                        s
                                        []
                                        [nm, show i]
                                        Nothing
                                        Nothing
                                        (finish [])
                  loop (i+1) (accum .&& s) ss

              loop _ accum [] = pure accum

          -- Get the schema
          indSchema <- loop (1::Int) sTrue inductionProofSteps

          -- Do the final proof:
          queryDebug [nm ++ ": Induction, proving inductive step:"]
          checkSatThen cfg kdSt "Step"
                                True
                                (Just (inductionIntros .=> indSchema))
                                inductiveStep
                                []
                                [nm, "Step"]
                                Nothing
                                Nothing $ \d -> do
            mbElapsed <- getElapsedTime mbStartTime
            finish (catMaybes [mbElapsed]) d
            pure $ Proof { rootOfTrust = ros
                         , isUserAxiom = False
                         , getProof    = label nm $ quantifiedBool result
                         , getProp     = toDyn result
                         , proofName   = nm
                         }

-- | Induction over 'SInteger'.
instance   (KnownSymbol nk, EqSymbolic z)
        => Inductive (Forall nk Integer -> SBool)
                     (SInteger -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate k = result (Forall k)
           nk          = symbolVal (Proxy @nk)

       k <- free nk

       let ih = internalAxiom "IH" $ predicate k
           (intros, pSteps) = mkCalcSteps $ steps ih k

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate 0
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ "+1)") (predicate (k+1))
              }

-- | Induction over 'SInteger' taking an extra argument.
instance    ( KnownSymbol na, SymVal a
            , KnownSymbol nk, EqSymbolic z)
         => Inductive (Forall na a -> Forall nk Integer -> SBool)
                      (SBV a -> SInteger -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate a k = result (Forall a) (Forall k)
           na            = symbolVal (Proxy @na)
           nk            = symbolVal (Proxy @nk)

       a <- free na
       k <- free nk

       let ih = internalAxiom "IH" $ \(Forall @"A" a') -> predicate a' k
           (intros, pSteps) = mkCalcSteps $ steps ih a k

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate a 0
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           =     observeIf not ("P(" ++ nk ++ "+1)") (predicate a (k+1))
                                          .&& observeIf not ("P(" ++ nk ++ "-1)") (predicate a (k-1))
              }

-- | Induction over 'SInteger' taking two extra arguments.
instance    ( KnownSymbol na, SymVal a
            , KnownSymbol nb, SymVal b
            , KnownSymbol nk, EqSymbolic z)
         => Inductive (Forall na a -> Forall nb b -> Forall nk Integer -> SBool)
                      (SBV a -> SBV b -> SInteger -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate a b k = result (Forall a) (Forall b) (Forall k)
           na              = symbolVal (Proxy @na)
           nb              = symbolVal (Proxy @nb)
           nk              = symbolVal (Proxy @nk)

       a <- free na
       b <- free nb
       k <- free nk

       let ih = internalAxiom "IH" $ \(Forall @"A" a') (Forall @"B" b') -> predicate a' b' k
           (intros, pSteps) = mkCalcSteps $ steps ih a b k

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate a b 0
              , inductionProofSteps     = pSteps
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
                      (SBV a -> SBV b -> SBV c -> SInteger -> (SBool, [ProofStep z]))
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

       let ih = internalAxiom "IH" $ \(Forall @"A" a') (Forall @"B" b') (Forall @"C" c') -> predicate a' b' c' k
           (intros, pSteps) = mkCalcSteps $ steps ih a b c k

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate a b c 0
              , inductionProofSteps     = pSteps
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
                      (SBV a -> SBV b -> SBV c -> SBV d -> SInteger -> (SBool, [ProofStep z]))
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

       let ih = internalAxiom "IH" $ \(Forall @"A" a') (Forall @"B" b') (Forall @"C" c') (Forall @"D" d') -> predicate a' b' c' d' k
           (intros, pSteps) = mkCalcSteps $ steps ih a b c d k

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate a b c d 0
              , inductionProofSteps     = pSteps
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
                     (SBV k -> SList k -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate k = result (Forall k)
           nks         = symbolVal (Proxy @nk)
           nk          = singular nks

       k  <- free nk
       ks <- free nks

       let ih = internalAxiom "IH" $ predicate ks
           (intros, pSteps) = mkCalcSteps $ steps ih k ks

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate SL.nil
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate (k SL..: ks))
              }

-- | Induction over 'SList' taking an extra argument
instance   ( KnownSymbol na, SymVal a
           , KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall na a -> Forall nk [k] -> SBool)
                     (SBV a -> SBV k -> SList k -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate a k = result (Forall a) (Forall k)
           na            = symbolVal (Proxy @na)
           nks           = symbolVal (Proxy @nk)
           nk            = singular nks

       a  <- free na
       k  <- free nk
       ks <- free nks

       let ih = internalAxiom "IH" $ \(Forall @"A" a') -> predicate a' ks
           (intros, pSteps) = mkCalcSteps $ steps ih a k ks

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate a SL.nil
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate a (k SL..: ks))
              }

-- | Induction over 'SList' taking two extra arguments
instance   ( KnownSymbol na, SymVal a
           , KnownSymbol nb, SymVal b
           , KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall na a -> Forall nb b -> Forall nk [k] -> SBool)
                     (SBV a -> SBV b -> SBV k -> SList k -> (SBool, [ProofStep z]))
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

       let ih = internalAxiom "IH" $ \(Forall @"A" a') (Forall @"B" b') -> predicate a' b' ks
           (intros, pSteps) = mkCalcSteps $ steps ih a b k ks

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate a b SL.nil
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nks ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ ":" ++ nks ++ ")") (predicate a b (k SL..: ks))
              }

-- | Induction over 'SList' taking three extra arguments
instance   ( KnownSymbol na, SymVal a
           , KnownSymbol nb, SymVal b
           , KnownSymbol nc, SymVal c
           , KnownSymbol nk, SymVal k, EqSymbolic z)
        => Inductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nk [k] -> SBool)
                     (SBV a -> SBV b -> SBV c -> SBV k -> SList k -> (SBool, [ProofStep z]))
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

       let ih = internalAxiom "IH" $ \(Forall @"A" a') (Forall @"B" b') (Forall @"C" c') -> predicate a' b' c' ks
           (intros, pSteps) = mkCalcSteps $ steps ih a b c k ks

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate a b c SL.nil
              , inductionProofSteps     = pSteps
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
                     (SBV a -> SBV b -> SBV c -> SBV d -> SBV k -> SList k -> (SBool, [ProofStep z]))
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

       let ih = internalAxiom "IH" $ \(Forall @"A" a') (Forall @"B" b') (Forall @"C" c') (Forall @"D" d') -> predicate a' b' c' d' ks
           (intros, pSteps) = mkCalcSteps $ steps ih a b c d k ks

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate a b c d SL.nil
              , inductionProofSteps     = pSteps
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

-- | Unicode alternative for `=:`:
(≡) :: ChainStep a (ChainsTo a) =>  a -> ChainsTo a -> ChainsTo a
(≡) = (=:)
infixr 1 ≡

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

-- | Alternative unicode for `|-`:
(⊢) :: SBool -> [ProofStep a] -> (SBool, [ProofStep a])
(⊢) = (|-)
infixl 0 ⊢
