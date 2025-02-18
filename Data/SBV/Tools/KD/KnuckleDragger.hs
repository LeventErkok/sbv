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
       , (|-), (⊢), (=:), (≡), (?), hyp, hprf, qed
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
  calcSteps :: a -> steps -> Symbolic (SBool, (SBool, [([Helper], SBool)]))

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
            (ros, modulo) = calculateRootOfTrust nm [p | HProof p <- stepHelpers]
            finish        = finishKD cfg ("Q.E.D." ++ modulo)

        mapM_ (qSaturateSavingObservables . getHelperBool) stepHelpers

        let go :: Int -> SBool -> [([Helper], SBool)] -> Query Proof
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

                 -- Prove that the assumptions follow, if any
                 case [a | HAssum a <- by] of
                   [] -> pure ()
                   as -> checkSatThen cfg kdSt "Asms  "
                                               True
                                               (Just calcIntros)
                                               (sAnd as)
                                               []
                                               ["", show i]
                                               (Just [nm, show i])
                                               Nothing
                                               (flip finish [])

                 queryDebug [nm ++ ": Proof step: " ++ show i ++ " to " ++ show (i+1) ++ ":"]
                 checkSatThen cfg kdSt "Step  "
                                       True
                                       (Just (sAnd (map getHelperBool by)))
                                       s
                                       []
                                       ["", show i]
                                       (Just [nm, show i])
                                       Nothing
                                       (flip finish [])

                 go (i+1) (s .&& accum) ss

        query $ go (1::Int) sTrue proofSteps

-- | Turn a sequence of steps into a chain of equalities
mkCalcSteps :: EqSymbolic a => (SBool, [ProofStep a]) -> (SBool, [([Helper], SBool)])
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
                                           , inductionProofSteps     :: [([Helper], SBool)]
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
             (ros, modulo) = calculateRootOfTrust nm [p | HProof p <- stepHelpers]
             finish et d   = finishKD cfg ("Q.E.D." ++ modulo) d et

         mapM_ (qSaturateSavingObservables . getHelperBool) stepHelpers

         query $ do

          queryDebug [nm ++ ": Induction, proving base case:"]
          checkSatThen cfg kdSt "Base" True (Just inductionIntros) inductionBaseCase [] [nm, "Base"] Nothing
                       (Just (liftIO (putStrLn inductionBaseFailureMsg)))
                       (finish [])

          let loop i accum ((by, s):ss) = do

                  -- Prove that the assumptions follow, if any
                  case [a | HAssum a <- by] of
                    [] -> pure ()
                    as -> checkSatThen cfg kdSt "Asms"
                                                True
                                                (Just inductionIntros)
                                                (sAnd as)
                                                []
                                                ["", show i]
                                                (Just [nm, show i])
                                                Nothing
                                                (finish [])

                  queryDebug [nm ++ ": Induction, proving step: " ++ show i]
                  checkSatThen cfg kdSt "Step"
                                        True
                                        (Just (sAnd (map getHelperBool by)))
                                        s
                                        []
                                        ["", show i]
                                        (Just [nm, show i])
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
instance (KnownSymbol nk, EqSymbolic z) => Inductive (Forall nk Integer -> SBool) (SInteger -> (SBool, [ProofStep z])) where
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
instance forall na a nk z. (KnownSymbol na, SymVal a, KnownSymbol nk, EqSymbolic z)
      => Inductive (Forall nk Integer -> Forall na a -> SBool)
                   (SInteger -> SBV a -> (SBool, [ProofStep z])) where
   inductionStrategy result steps = do
       let predicate k a = result (Forall k) (Forall a)
           nk            = symbolVal (Proxy @nk)
           na            = symbolVal (Proxy @na)

       k <- free nk
       a <- free na

       let ih = internalAxiom "IH" $ \a' -> result (Forall k) (a' :: Forall na a)
           (intros, pSteps) = mkCalcSteps $ steps ih k a

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate 0 a
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ "+1)") (predicate (k+1) a)
              }

-- | Induction over 'SInteger' taking two extra arguments.
instance forall na a nb b nk z. (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nk, EqSymbolic z)
      => Inductive (Forall nk Integer -> Forall na a -> Forall nb b -> SBool)
                   (SInteger -> SBV a -> SBV b -> (SBool, [ProofStep z])) where
   inductionStrategy result steps = do
       let predicate k a b = result (Forall k) (Forall a) (Forall b)
           nk              = symbolVal (Proxy @nk)
           na              = symbolVal (Proxy @na)
           nb              = symbolVal (Proxy @nb)

       k <- free nk
       a <- free na
       b <- free nb

       let ih = internalAxiom "IH" $ \a' b' -> result (Forall k) (a' :: Forall na a) (b' :: Forall nb b)
           (intros, pSteps) = mkCalcSteps $ steps ih k a b

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate 0 a b
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ "+1)") (predicate (k+1) a b)
              }

-- | Induction over 'SInteger' taking three extra arguments.
instance forall na a nb b nc c nk z. (KnownSymbol na, SymVal a , KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nk, EqSymbolic z)
     => Inductive (Forall nk Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool)
                  (SInteger -> SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate k a b c = result (Forall k) (Forall a) (Forall b) (Forall c)
           nk                = symbolVal (Proxy @nk)
           na                = symbolVal (Proxy @na)
           nb                = symbolVal (Proxy @nb)
           nc                = symbolVal (Proxy @nc)

       k <- free nk
       a <- free na
       b <- free nb
       c <- free nc

       let ih = internalAxiom "IH" $ \a' b' c' -> result (Forall k) (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c)
           (intros, pSteps) = mkCalcSteps $ steps ih k a b c

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate 0 a b c
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ "+1)") (predicate (k+1) a b c)
              }

-- | Induction over 'SInteger' taking four extra arguments.
instance forall na a nb b nc c nd d nk z. (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol nk, EqSymbolic z)
      => Inductive (Forall nk Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                   (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z])) where
   inductionStrategy result steps = do
       let predicate k a b c d = result (Forall k) (Forall a) (Forall b) (Forall c) (Forall d)
           nk                  = symbolVal (Proxy @nk)
           na                  = symbolVal (Proxy @na)
           nb                  = symbolVal (Proxy @nb)
           nc                  = symbolVal (Proxy @nc)
           nd                  = symbolVal (Proxy @nd)

       k <- free nk
       a <- free na
       b <- free nb
       c <- free nc
       d <- free nd

       let ih = internalAxiom "IH" $ \a' b' c' d' -> result (Forall k) (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c) (d' :: Forall nd d)
           (intros, pSteps) = mkCalcSteps $ steps ih k a b c d

       pure InductionStrategy {
                inductionIntros         = k .>= 0 .&& intros
              , inductionBaseCase       = predicate 0 a b c d
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nk ++ " = 0."
              , inductiveStep           = observeIf not ("P(" ++ nk ++ "+1)") (predicate (k+1) a b c d)
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
instance (KnownSymbol nk, SymVal k, EqSymbolic z)
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
instance forall na a nx x z. (KnownSymbol na, SymVal a, KnownSymbol nx, SymVal x, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall na a -> SBool)
                   (SBV x -> SList x -> SBV a -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate xs a = result (Forall xs) (Forall a)
           na             = symbolVal (Proxy @na)
           nxs            = symbolVal (Proxy @nx)
           nx             = singular nxs

       x  <- free nx
       xs <- free nxs
       a  <- free na

       let ih = internalAxiom "IH" $ \a' -> result (Forall xs) (a' :: Forall na a)
           (intros, pSteps) = mkCalcSteps $ steps ih x xs a

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate SL.nil a
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nxs ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ")") (predicate (x SL..: xs) a)
              }

-- | Induction over 'SList' taking two extra arguments
instance forall na a nb b nx x z. (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nx, SymVal x, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall na a -> Forall nb b -> SBool)
                   (SBV x -> SList x -> SBV a -> SBV b -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate xs a b = result (Forall xs) (Forall a) (Forall b)
           na               = symbolVal (Proxy @na)
           nb               = symbolVal (Proxy @nb)
           nxs              = symbolVal (Proxy @nx)
           nx               = singular nxs

       x  <- free nx
       xs <- free nxs
       a  <- free na
       b  <- free nb

       let ih = internalAxiom "IH" $ \a' b' -> result (Forall xs) (a' :: Forall na a) (b' :: Forall nb b)
           (intros, pSteps) = mkCalcSteps $ steps ih x xs a b

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate SL.nil a b
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nxs ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ")") (predicate (x SL..: xs) a b)
              }

-- | Induction over 'SList' taking three extra arguments
instance forall na a nb b nc c nx x z. (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nx, SymVal x, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool)
                   (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate xs a b c = result (Forall xs) (Forall a) (Forall b) (Forall c)
           na                 = symbolVal (Proxy @na)
           nb                 = symbolVal (Proxy @nb)
           nc                 = symbolVal (Proxy @nc)
           nxs                = symbolVal (Proxy @nx)
           nx                 = singular nxs

       x  <- free nx
       xs <- free nxs
       a  <- free na
       b  <- free nb
       c  <- free nc

       let ih = internalAxiom "IH" $ \a' b' c' -> result (Forall xs) (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c)
           (intros, pSteps) = mkCalcSteps $ steps ih x xs a b c

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate SL.nil a b c
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nxs ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ")") (predicate (x SL..: xs) a b c)
              }

-- | Induction over 'SList' taking four extra arguments
instance forall na a nb b nc c nd d nx x z. (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol nx, SymVal x, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                   (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate xs a b c d = result (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d)
           na                   = symbolVal (Proxy @na)
           nb                   = symbolVal (Proxy @nb)
           nc                   = symbolVal (Proxy @nc)
           nd                   = symbolVal (Proxy @nd)
           nxs                  = symbolVal (Proxy @nx)
           nx                   = singular nxs

       x  <- free nx
       xs <- free nxs
       a  <- free na
       b  <- free nb
       c  <- free nc
       d  <- free nd

       let ih = internalAxiom "IH" $ \a' b' c' d' -> result (Forall xs) (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c) (d' :: Forall nd d)
           (intros, pSteps) = mkCalcSteps $ steps ih x xs a b c d

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate SL.nil a b c d
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nxs ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ")") (predicate (x SL..: xs) a b c d)
              }

-- | Induction over 'SList' taking five extra arguments
instance forall na a nb b nc c nd d ne e nx x z. (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, KnownSymbol nx, SymVal x, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool)
                   (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z]))
 where
   inductionStrategy result steps = do
       let predicate xs a b c d e = result (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)
           na                     = symbolVal (Proxy @na)
           nb                     = symbolVal (Proxy @nb)
           nc                     = symbolVal (Proxy @nc)
           nd                     = symbolVal (Proxy @nd)
           ne                     = symbolVal (Proxy @ne)
           nxs                    = symbolVal (Proxy @nx)
           nx                     = singular nxs

       x  <- free nx
       xs <- free nxs
       a  <- free na
       b  <- free nb
       c  <- free nc
       d  <- free nd
       e  <- free ne

       let ih = internalAxiom "IH" $ \a' b' c' d' e' -> result (Forall xs) (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c) (d' :: Forall nd d) (e' :: Forall ne e)
           (intros, pSteps) = mkCalcSteps $ steps ih x xs a b c d e

       pure InductionStrategy {
                inductionIntros         = intros
              , inductionBaseCase       = predicate SL.nil a b c d e
              , inductionProofSteps     = pSteps
              , inductionBaseFailureMsg = "Property fails for " ++ nxs ++ " = []."
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ")") (predicate (x SL..: xs) a b c d e)
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

-- | Helpers for a step
data Helper = HProof Proof  -- A previously proven theorem
            | HAssum SBool  -- A hypothesis

-- | Smart constructor for creating a helper from a boolean. This is hardly needed, unless you're
-- mixing proofs and booleans in one group of hints.
hyp :: SBool -> Helper
hyp = HAssum

-- | Smart constructor for creating a helper from a boolean. This is hardly needed, unless you're
-- mixing proofs and booleans in one group of hints.
hprf :: Proof -> Helper
hprf = HProof

-- | Get the underlying boolean of a helper
getHelperBool :: Helper -> SBool
getHelperBool (HProof p) = getProof p
getHelperBool (HAssum b) = b

-- | A proof-step with associated helpers
data ProofStep a = ProofStep a [Helper]

-- | Class capturing giving a proof-step helper
class ProofHint a b where
  -- | Specify a helper for the given proof step
  (?) :: a -> b -> ProofStep a
  infixl 2 ?

-- | Giving just one proof as a helper.
instance ProofHint a Proof where
  a ? p = ProofStep a [HProof p]

-- | Giving just one boolean as a helper.
instance ProofHint a SBool where
  a ? p = ProofStep a [HAssum p]

-- | Giving just one helper
instance ProofHint a Helper where
  a ? h = ProofStep a [h]

-- | Giving a bunch of proofs as a helper.
instance ProofHint a [Proof] where
  a ? ps = ProofStep a (map HProof ps)

-- | Giving a bunch of booleans as a helper.
instance ProofHint a [SBool] where
  a ? ps = ProofStep a (map HAssum ps)

-- | Giving a set of helpers
instance ProofHint a [Helper] where
  a ? hs = ProofStep a hs

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

-- | Start a calculational proof, with the given hypothesis. Use @[]@ as the
-- first argument if the calculation holds unconditionally. The first argument is
-- typically used to introduce hypotheses in proofs of implications such as @A .=> B .=> C@, where
-- we would put @[A, B]@ as the starting assumption. You can name these and later use in the derivation steps.
(|-) :: [SBool] -> [ProofStep a] -> (SBool, [ProofStep a])
bs |- ps = (sAnd bs, ps)
infixl 0 |-

-- | Alternative unicode for `|-`:
(⊢) :: [SBool] -> [ProofStep a] -> (SBool, [ProofStep a])
(⊢) = (|-)
infixl 0 ⊢
