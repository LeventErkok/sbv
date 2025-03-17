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
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KD.KnuckleDragger (
         Proposition, Proof, Instantiatable(..), Inst(..)
       , axiom
       , lemma,   lemmaWith
       , theorem, theoremWith
       ,    calc,    calcWith,    calcThm,    calcThmWith
       ,  induct,  inductWith,  inductThm,  inductThmWith
       , sInduct, sInductWith, sInductThm, sInductThmWith
       , sorry
       , KD, runKD, runKDWith, use
       , (|-), (⊢), (=:), (≡), (??), (⁇), cases, hyp, hprf, qed
       ) where

import Data.SBV
import Data.SBV.Core.Model (qSaturateSavingObservables)

import Data.SBV.Control hiding (getProof)

import Data.SBV.Core.Data(SolverContext)

import Data.SBV.Tools.KD.Kernel
import Data.SBV.Tools.KD.Utils

import qualified Data.SBV.List as SL

import Control.Monad (forM_, zipWithM_)
import Control.Monad.Trans (liftIO, MonadIO)

import Data.Char (isSpace)
import Data.List (isPrefixOf, isSuffixOf, intercalate)
import Data.Maybe (catMaybes, maybeToList)

import Data.Proxy
import GHC.TypeLits (KnownSymbol, symbolVal, Symbol)

import Data.SBV.Utils.TDiff

import Data.Dynamic
import Data.Time (NominalDiffTime)

-- | Bring an IO proof into current proof context.
use :: IO Proof -> KD Proof
use = liftIO

-- | Captures the steps for a calculationa proof
data CalcStrategy = CalcStrategy { calcIntros     :: SBool
                                 , calcProofSteps :: [([Helper], SBool)]
                                 , calcResult     :: SBool
                                 }

-- | Saturatable things in steps
proofStepSaturatables :: [([Helper], SBool)] -> [SBool]
proofStepSaturatables = concatMap getS
  where getS (hs, b) = b : concatMap getH hs
        getH (HelperProof  p)  = [getProof p]
        getH (HelperAssum  b)  = [b]
        getH (HelperCase _ ss) = ss

-- | Things that are inside calc-strategy that we have to saturate
getCalcStrategySaturatables :: CalcStrategy -> [SBool]
getCalcStrategySaturatables (CalcStrategy calcIntros calcProofSteps calcResult) = calcIntros : calcResult : proofStepSaturatables calcProofSteps

-- | Based on the helpers given, construct the proofs we have to do in the given case
stepCases :: Int -> [Helper] -> Either (String, SBool) ([(String, SBool)], SBool)
stepCases i helpers
   | hasCase
   = Right (caseSplits, cover)
   | True
   = Left (show i, sAnd (map getBools helpers))
  where join :: [(String, SBool)] -> Helper -> [(String, SBool)]
        join sofar (HelperProof p)     =       map (\(n, cond) -> (n, cond .&& getProof p)) sofar
        join sofar (HelperAssum b)     =       map (\(n, cond) -> (n, cond .&&          b)) sofar
        join sofar (HelperCase  cn cs) = concatMap (\(n, cond) -> [ (dotN n ++ cn ++ "[" ++ show j ++ "]", cond .&& b)
                                                                  | (j, b) <- zip [(1::Int)..] cs
                                                                  ]) sofar

        -- Add a dot if we have a legit prefix
        dotN "" = ""
        dotN s  = s ++ "."

        -- Used only when we have ano case splits:
        getBools (HelperProof p) = getProof p
        getBools (HelperAssum b) = b
        getBools (HelperCase{})  = error "Unexpected case in stepCases: Wasn't expecting to see a HelperCase here."

        -- All case-splits. If there isn't any, we'll get just one case
        caseSplits = foldl join [("", sTrue)] helpers

        -- If there were any cases, then we also need coverage
        isCase (HelperProof {}) = False
        isCase (HelperAssum {}) = False
        isCase (HelperCase  {}) = True

        hasCase = any isCase helpers

        regulars = concatMap getHyp helpers
          where getHyp (HelperProof p)  = [getProof p]
                getHyp (HelperAssum b)  = [b]
                getHyp (HelperCase  {}) = []

        cover = sAnd regulars .&& sNot (sOr [b | (_, b) <- caseSplits])

-- | Propagate the settings for ribbon/timing from top to current. Because in any subsequent configuration
-- in a lemmaWith, inductWith etc., we just want to change the solver, not the actual settings for KD.
kdMergeCfg :: SMTConfig -> SMTConfig -> SMTConfig
kdMergeCfg cur top = cur{kdOptions = kdOptions top}

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
  calcSteps :: a -> steps -> Symbolic (SBool, CalcStrategy)

  calc            nm p steps = getKDConfig >>= \cfg  -> calcWith          cfg                   nm p steps
  calcThm         nm p steps = getKDConfig >>= \cfg  -> calcThmWith       cfg                   nm p steps
  calcWith    cfg nm p steps = getKDConfig >>= \cfg' -> calcGeneric False (kdMergeCfg cfg cfg') nm p steps
  calcThmWith cfg nm p steps = getKDConfig >>= \cfg' -> calcGeneric True  (kdMergeCfg cfg cfg') nm p steps

  calcGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> KD Proof
  calcGeneric tagTheorem cfg@SMTConfig{kdOptions = KDOptions{measureTime}} nm result steps = do
     kdSt <- getKDState

     liftIO $ runSMTWith cfg $ do

        qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

        message cfg $ (if tagTheorem then "Theorem" else "Lemma") ++ ": " ++ nm ++ "\n"

        mbStartTime <- getTimeStampIf measureTime

        (calcGoal, strategy@CalcStrategy {calcIntros, calcProofSteps, calcResult}) <- calcSteps result steps

        let stepHelpers = concatMap fst calcProofSteps

            finish et helpers d = finishKD cfg ("Q.E.D." ++ modulo) d et
              where (_, modulo) = calculateRootOfTrust nm helpers

        -- Collect all subterms and saturate them
        mapM_ qSaturateSavingObservables $ calcIntros : getCalcStrategySaturatables strategy

        query $ do

           let proveStep i (by, s) = do

                    -- Prove that the assumptions follow, if any
                    case getHelperAssumes by of
                      [] -> pure ()
                      as -> checkSatThen cfg kdSt "Asms  "
                                                  True
                                                  (Just calcIntros)
                                                  (sAnd as)
                                                  []
                                                  ["", show i]
                                                  (Just [nm, show i, "Assumptions"])
                                                  (finish [] [])

                    queryDebug [nm ++ ": Proof step: " ++ show i ++ " to " ++ show (i+1) ++ ":"]

                    proveAllCases i cfg kdSt (stepCases i by) "Step  " s nm (finish [] (getHelperProofs by))

           zipWithM_ proveStep [1::Int ..] calcProofSteps

           queryDebug [nm ++ ": Proof end: proving the result:"]

           checkSatThen cfg kdSt "Result" True
                        (Just (calcIntros .=> calcResult))
                        calcGoal
                        []
                        ["", ""]
                        (Just [nm, "Result"]) $ \d ->
                          do mbElapsed <- getElapsedTime mbStartTime
                             let (ros, modulo) = calculateRootOfTrust nm (getHelperProofs stepHelpers)
                             finishKD cfg ("Q.E.D." ++ modulo) d (catMaybes [mbElapsed])

                             pure Proof { rootOfTrust = ros
                                        , isUserAxiom = False
                                        , getProof    = label nm (quantifiedBool result)
                                        , getProp     = toDyn result
                                        , proofName   = nm
                                        }

proveAllCases :: (Monad m, SolverContext m, MonadIO m, MonadQuery m, Proposition a)
              => Int -> SMTConfig -> KDState
              -> Either (String, SBool) ([(String, SBool)], SBool)
              -> String -> a -> String -> ((Int, Maybe NominalDiffTime) -> IO ()) -> m ()
proveAllCases topStep cfg kdSt caseInfo stepTag s nm finalize
  | Left (stepName, asmp) <- caseInfo
  = checker stepTag asmp s ["", stepName] (Just [nm, stepName])
  | Right (proofCases, coverCond) <- caseInfo
  = do let len   = length proofCases
           ways  = case len of
                     1 -> "one way"
                     n -> show n ++ " ways"

           slen  = show len
           clen  = length slen
           sh i  = reverse . take clen $ reverse (show i) ++ repeat ' '

       _tab <- liftIO $ startKD cfg True ("Step " ++ show topStep) ["", "Case split " ++ ways ++ ":"]

       forM_ (zip [(1::Int)..] proofCases) $ \(c, (stepName, asmp)) ->
             checker ("Case [" ++ sh c ++ " of " ++ show len ++ "]") asmp s ["", "", stepName] (Just [nm, stepName])

       checker "Completeness" coverCond s ["", "", ""] (Just [nm, show topStep, "Completeness"])
  where
     checker tag caseAsmp cond cnm fnm = checkSatThen cfg kdSt tag True (Just caseAsmp) cond [] cnm fnm finalize

-- | Turn a sequence of steps into a chain of equalities
mkCalcSteps :: EqSymbolic a => (SBool, [ProofStep a]) -> CalcStrategy
mkCalcSteps (intros, xs) = case reverse xs of
                             (SingleStep _ (_:_) : _) -> error $ unlines [ ""
                                                                         , "*** Incorrect calc/induct lemma calculations."
                                                                         , "***"
                                                                         , "***  The last step in the proof has a helper, which isn't used."
                                                                         , "***"
                                                                         , "*** Perhaps the hint is off-by-one in its placement?"
                                                                         ]
                             _                       -> CalcStrategy { calcIntros     = intros
                                                                     , calcProofSteps = zipWith merge xs (drop 1 xs)
                                                                     , calcResult     = calcResult
                                                                     }
  where merge (SingleStep a by) (SingleStep b _) = (by, a .== b)
        calcResult
          | length xs <= 1 = sTrue
          | True           = case (xs, reverse xs) of
                               (SingleStep a _ : _, SingleStep b _ : _) -> a .== b
                               _                                        -> sTrue

-- | Chaining lemmas that depend on no extra variables
instance EqSymbolic z => CalcLemma SBool (SBool, [ProofStep z]) where
   calcSteps result steps = pure (result, mkCalcSteps steps)

-- | Chaining lemmas that depend on a single extra variable.
instance (KnownSymbol na, SymVal a, EqSymbolic z) => CalcLemma (Forall na a -> SBool) (SBV a -> (SBool, [ProofStep z])) where
   calcSteps result steps = do a <- free (symbolVal (Proxy @na))
                               pure (result (Forall a), mkCalcSteps (steps a))

-- | Chaining lemmas that depend on two extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> SBool)
                   (SBV a -> SBV b -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                               pure (result (Forall a) (Forall b), mkCalcSteps (steps a b))

-- | Chaining lemmas that depend on three extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> SBool)
                   (SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b, c) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                               pure (result (Forall a) (Forall b) (Forall c), mkCalcSteps (steps a b c))

-- | Chaining lemmas that depend on four extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                   (SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b, c, d) <- (,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d), mkCalcSteps (steps a b c d))

-- | Chaining lemmas that depend on five extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool)
                   (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z])) where
   calcSteps result steps = do (a, b, c, d, e) <- (,,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e), mkCalcSteps (steps a b c d e))

-- | Captures the schema for an inductive proof. Base case might be nothing, to cover strong induction.
data InductionStrategy = InductionStrategy { inductionIntros         :: SBool
                                           , inductionBaseCase       :: Maybe SBool
                                           , inductionProofSteps     :: [([Helper], SBool)]
                                           , inductiveStep           :: SBool
                                           , inductiveResult         :: SBool
                                           }

-- | Are we doing strong induction or regular induction?
data InductionStyle = RegularInduction | StrongInduction

getInductionStrategySaturatables :: InductionStrategy -> [SBool]
getInductionStrategySaturatables (InductionStrategy inductionIntros
                                                    inductionBaseCase
                                                    inductionProofSteps
                                                    inductiveStep
                                                    inductiveResult)
  = inductionIntros : inductiveStep : inductiveResult : proofStepSaturatables inductionProofSteps ++ maybeToList inductionBaseCase

-- | A class for doing regular inductive proofs.
class Inductive a steps where
   -- | Inductively prove a lemma, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   induct  :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Inductively prove a theorem. Same as 'induct', but tagged as a theorem, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductThm :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'induct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'inductThm', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductThmWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   induct            nm p steps = getKDConfig >>= \cfg  -> inductWith                             cfg                   nm p steps
   inductThm         nm p steps = getKDConfig >>= \cfg  -> inductThmWith                          cfg                   nm p steps
   inductWith    cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine RegularInduction False (kdMergeCfg cfg cfg') nm p (inductionStrategy p steps)
   inductThmWith cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine RegularInduction True  (kdMergeCfg cfg cfg') nm p (inductionStrategy p steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL inductionStrategy #-}
   inductionStrategy :: Proposition a => a -> (Proof -> steps) -> Symbolic InductionStrategy

-- | A class for doing strong inductive proofs.
class SInductive a steps where
   -- | Inductively prove a lemma, using strong induction, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInduct :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Inductively prove a theorem, using strong induction. Same as 'sInduct', but tagged as a theorem, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductThm :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'sInduct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'sInductThm', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductThmWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   sInduct            nm p steps = getKDConfig >>= \cfg  -> sInductWith                          cfg                   nm p steps
   sInductThm         nm p steps = getKDConfig >>= \cfg  -> sInductThmWith                       cfg                   nm p steps
   sInductWith    cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine StrongInduction False (kdMergeCfg cfg cfg') nm p (sInductionStrategy p steps)
   sInductThmWith cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine StrongInduction True  (kdMergeCfg cfg cfg') nm p (sInductionStrategy p steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL sInductionStrategy #-}
   sInductionStrategy :: Proposition a => a -> (Proof -> steps) -> Symbolic InductionStrategy

-- | Do an inductive proof, based on the given strategy
inductionEngine :: Proposition a => InductionStyle -> Bool -> SMTConfig -> String -> a -> Symbolic InductionStrategy -> KD Proof
inductionEngine style tagTheorem cfg@SMTConfig{kdOptions = KDOptions{measureTime}} nm result getStrategy = do
   kdSt <- getKDState

   liftIO $ runSMTWith cfg $ do

      qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

      let strong = case style of
                     RegularInduction -> ""
                     StrongInduction  -> " (strong)"

      message cfg $ "Inductive " ++ (if tagTheorem then "theorem" else "lemma") ++ strong ++ ": " ++ nm ++ "\n"

      strategy@InductionStrategy { inductionIntros
                                 , inductionBaseCase
                                 , inductionProofSteps
                                 , inductiveStep
                                 , inductiveResult
                                 } <- getStrategy

      mbStartTime <- getTimeStampIf measureTime

      let stepHelpers = concatMap fst inductionProofSteps

          finish et helpers d = finishKD cfg ("Q.E.D." ++ modulo) d et
            where (_, modulo) = calculateRootOfTrust nm helpers

      -- Collect all subterms and saturate them
      mapM_ qSaturateSavingObservables $ getInductionStrategySaturatables strategy

      query $ do

       case inductionBaseCase of
          Nothing -> pure ()
          Just bc -> do queryDebug [nm ++ ": Induction, proving base case:"]
                        checkSatThen cfg kdSt "Base" True (Just inductionIntros) bc [] [nm, "Base"] Nothing (finish [] [])

       let proveStep i (by, s) = do

               -- Prove that the assumptions follow, if any
               case getHelperAssumes by of
                 [] -> pure ()
                 as -> checkSatThen cfg kdSt "Asms"
                                             True
                                             (Just inductionIntros)
                                             (sAnd as)
                                             []
                                             ["", show i]
                                             (Just [nm, show i, "Assumptions"])
                                             (finish [] [])

               queryDebug [nm ++ ": Induction, proving step: " ++ show i]

               proveAllCases i cfg kdSt (stepCases i by) "Step" s nm (finish [] (getHelperProofs by))

       -- Do the steps
       zipWithM_ proveStep [1::Int ..] inductionProofSteps

       -- Do the final proof:
       queryDebug [nm ++ ": Induction, proving inductive step:"]
       checkSatThen cfg kdSt "Step"
                             True
                             (Just (inductionIntros .=> inductiveResult))
                             inductiveStep
                             []
                             [nm, "Step"]
                             Nothing $ \d -> do

         mbElapsed <- getElapsedTime mbStartTime

         let (ros, modulo) = calculateRootOfTrust nm (getHelperProofs stepHelpers)
         finishKD cfg ("Q.E.D." ++ modulo) d (catMaybes [mbElapsed])

         pure $ Proof { rootOfTrust = ros
                      , isUserAxiom = False
                      , getProof    = label nm $ quantifiedBool result
                      , getProp     = toDyn result
                      , proofName   = nm
                      }

-- Induction strategy helper
mkIndStrategy :: EqSymbolic a => Maybe SBool -> Maybe SBool -> (SBool, [ProofStep a]) -> SBool -> InductionStrategy
mkIndStrategy mbExtraConstraint mbBaseCase indSteps step =
        let CalcStrategy { calcIntros, calcProofSteps, calcResult } = mkCalcSteps indSteps
        in InductionStrategy { inductionIntros     = maybe id (.&&) mbExtraConstraint calcIntros
                             , inductionBaseCase   = mbBaseCase
                             , inductionProofSteps = calcProofSteps
                             , inductiveStep       = step
                             , inductiveResult     = calcResult
                             }

-- | Create a new variable with the given name, return both the variable and the name
mkVar :: (KnownSymbol n, SymVal a) => proxy n -> Symbolic (SBV a, String)
mkVar x = do let nn = symbolVal x
             n <- free nn
             pure (n, nn)

-- | Create a new variable with the given name, return both the variable and the name. List version.
mkLVar :: (KnownSymbol n, SymVal a) => proxy n -> Symbolic (SBV a, SList a, String)
mkLVar x = do let nxs = symbolVal x
                  nx  = singular nxs
              e  <- free nx
              es <- free nxs
              pure (e, es, nx ++ ":" ++ nxs)

-- | Helper for induction result
indResult :: [String] -> SBool -> SBool
indResult nms = observeIf not ("P(" ++ intercalate ", " nms ++ ")")

-- | Induction over 'SInteger'
instance (KnownSymbol nn, EqSymbolic z) => Inductive (Forall nn Integer -> SBool) (SInteger -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0)))
                            (steps (internalAxiom "IH" (result (Forall n))) n)
                            (indResult [nn ++ "+1"] (result (Forall (n+1))))

-- | Strong induction over 'SInteger'
instance (KnownSymbol nn, EqSymbolic z) => SInductive (Forall nn Integer -> SBool) (SInteger -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) -> 0 .<= n' .&& n' .< n .=> result (Forall n'))) n)
                            (indResult [nn] (result (Forall n)))

-- | Induction over 'SInteger', taking an extra argument
instance (KnownSymbol nn, KnownSymbol na, SymVal a, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> SBool) (SInteger -> SBV a -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall n) (Forall a'))) n a)
                            (indResult [nn ++ "+1", na] (result (Forall (n+1)) (Forall a)))

-- | Strong induction over 'SInteger', taking an extra argument
instance (KnownSymbol nn, KnownSymbol na, SymVal a, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> SBool) (SInteger -> SBV a -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a'))) n a)
                            (indResult [nn, na] (result (Forall n) (Forall a)))

-- | Induction over 'SInteger', taking two extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) (SInteger -> SBV a -> SBV b -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall n) (Forall a') (Forall b'))) n a b)
                            (indResult [nn ++ "+1", na, nb] (result (Forall (n+1)) (Forall a) (Forall b)))

-- | Strong induction over 'SInteger', taking two extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) (SInteger -> SBV a -> SBV b -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b'))) n a b)
                            (indResult [nn, na, nb] (result (Forall n) (Forall a) (Forall b)))

-- | Induction over 'SInteger', taking three extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall n) (Forall a') (Forall b') (Forall c'))) n a b c)
                            (indResult [nn ++ "+1", na, nb, nc] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c)))

-- | Strong induction over 'SInteger', taking three extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b') (Forall c'))) n a b c)
                            (indResult [nn, na, nb, nc] (result (Forall n) (Forall a) (Forall b) (Forall c)))

-- | Induction over 'SInteger', taking four extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d'))) n a b c d)
                            (indResult [nn ++ "+1", na, nb, nc, nd] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Strong induction over 'SInteger', taking four extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b') (Forall c') (Forall d'))) n a b c d)
                            (indResult [nn, na, nb, nc, nd] (result (Forall n) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Induction over 'SInteger', taking five extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       (e, ne) <- mkVar (Proxy @ne)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) n a b c d e)
                            (indResult [nn ++ "+1", na, nb, nc, nd, ne] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- | Strong induction over 'SInteger', taking five extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       (e, ne) <- mkVar (Proxy @ne)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) n a b c d e)
                            (indResult [nn, na, nb, nc, nd, ne] (result (Forall n) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- Given a user name for the list, get a name for the element, in the most suggestive way possible
--   xs  -> x
--   xss -> xs
--   foo -> fooElt
singular :: String -> String
singular n = case reverse n of
               's':_:_ -> init n
               _       -> n ++ "Elt"

-- | Metric for induction over lists. Currently we simply require the list we're assuming correctness for is shorter in length, which
-- is a measure that is guarenteed >= 0. Later on, we might want to generalize this to a user given measure.
lexLeq :: SymVal a => SList a -> SList a -> SBool
lexLeq xs ys = SL.length xs .< SL.length ys

{-
-- | Metric for induction over two lists. We use lexicographic ordering. 
lexLeq2 :: (SymVal a, SymVal b) => (SList a, SList b) -> (SList a, SList b) -> SBool
lexLeq2 (xs', ys') (xs, ys) =   lxs' .<  lxs        -- First one got smaller
                            .|| (    lxs' .== lxs   -- OR, the first one did not grow
                                 .&& lys' .<  lys   -- and the second went down
                                )
 where lxs' = SL.length xs'
       lys' = SL.length ys'
       lxs  = SL.length xs
       lys  = SL.length ys
-}

-- | Induction over 'SList'
instance (KnownSymbol nxs, SymVal x, EqSymbolic z) => Inductive (Forall nxs [x] -> SBool) (SBV x -> SList x -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil)))
                            (steps (internalAxiom "IH" (result (Forall xs))) x xs)
                            (indResult [nxxs] (result (Forall (x SL..: xs))))

-- | Strong induction over 'SList'
instance (KnownSymbol nxs, SymVal x, EqSymbolic z) => SInductive (Forall nxs [x] -> SBool) (SBV x -> SList x -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) -> xs' `lexLeq` xs .=> result (Forall xs'))) x xs)
                            (indResult [nxxs] (result (Forall (x SL..: xs))))

-- | Induction over 'SList', taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> SBool) (SBV x -> SList x -> SBV a -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall xs) (Forall a'))) x xs a)
                            (indResult [nxxs, na] (result (Forall (x SL..: xs)) (Forall a)))

-- | Strong induction over 'SList', taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> SBool) (SBV x -> SList x -> SBV a -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a'))) x xs a)
                            (indResult [nxxs, na] (result (Forall (x SL..: xs)) (Forall a)))

-- | Induction over 'SList', taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall xs) (Forall a') (Forall b'))) x xs a b)
                            (indResult [nxxs, na, nb] (result (Forall (x SL..: xs)) (Forall a) (Forall b)))

-- | Strong induction over 'SList', taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b'))) x xs a b)
                            (indResult [nxxs, na, nb] (result (Forall (x SL..: xs)) (Forall a) (Forall b)))

-- | Induction over 'SList', taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall xs) (Forall a') (Forall b') (Forall c'))) x xs a b c)
                            (indResult [nxxs, na, nb, nc] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c)))

-- | Strong induction over 'SList', taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b') (Forall c'))) x xs a b c)
                            (indResult [nxxs, na, nb, nc] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c)))

-- | Induction over 'SList', taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d'))) x xs a b c d)
                            (indResult [nxxs, na, nb, nc, nd] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Strong induction over 'SList', taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b') (Forall c') (Forall d'))) x xs a b c d)
                            (indResult [nxxs, na, nb, nc, nd] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Induction over 'SList', taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z])) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       (e, ne)       <- mkVar  (Proxy @ne)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) x xs a b c d e)
                            (indResult [nxxs, na, nb, nc, nd, ne] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- | Strong induction over 'SList', taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z])) where
  sInductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       (e, ne)       <- mkVar  (Proxy @ne)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) x xs a b c d e)
                            (indResult [nxxs, na, nb, nc, nd, ne] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

{-------------
-- | Induction over two lists, simultaneously
instance (KnownSymbol nx, SymVal x, KnownSymbol ny, SymVal y, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall ny [y] -> SBool)
                   (SBV x -> SList x -> SBV y -> SList y -> (SBool, [ProofStep z]))
  where
   inductionStrategy style result steps = do
       let predicate xs ys = result (Forall xs) (Forall ys)
           nxs             = symbolVal (Proxy @nx)
           nx              = singular nxs
           nys             = symbolVal (Proxy @ny)
           ny              = singular nys

       x  <- free nx
       xs <- free nxs

       y  <- free ny
       ys <- free nys

       let ih = case style of
                  RegularInduction -> internalAxiom "IH" $                                                                                                   result (Forall xs)  (Forall ys)
                  StrongInduction  -> internalAxiom "IH" $ \(Forall xs' :: Forall nx [x]) (Forall ys' :: Forall ny [y]) -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs') (Forall ys')
           CalcStrategy { calcIntros, calcProofSteps, calcResult } = mkCalcSteps $ steps ih x xs y ys

       pure InductionStrategy {
                inductionIntros         = calcIntros
              , inductionBaseCase       = mkBaseCase style $ predicate SL.nil SL.nil .&& predicate SL.nil (y SL..: ys) .&& predicate (x SL..: xs) SL.nil
              , inductionProofSteps     = calcProofSteps
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ", " ++ ny ++ ":" ++ nys ++ ")") (predicate (x SL..: xs) (y SL..: ys))
              , inductiveResult         = calcResult
              }

-- | Induction over two lists, simultaneously, taking one extra argument
instance (KnownSymbol nx, SymVal x, KnownSymbol ny, SymVal y, KnownSymbol na, SymVal a, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall ny [y] -> Forall na a -> SBool)
                   (SBV x -> SList x -> SBV y -> SList y -> SBV a -> (SBool, [ProofStep z]))
  where
   inductionStrategy style result steps = do
       let predicate xs ys a = result (Forall xs) (Forall ys) (Forall a)
           nxs               = symbolVal (Proxy @nx)
           nx                = singular nxs
           nys               = symbolVal (Proxy @ny)
           ny                = singular nys
           na                = symbolVal (Proxy @na)

       x  <- free nx
       xs <- free nxs

       y  <- free ny
       ys <- free nys

       a  <- free na

       let ih = case style of
                  RegularInduction -> internalAxiom "IH" $ \                                                            a' ->                                   result (Forall xs)  (Forall ys)  (a' :: Forall na a)
                  StrongInduction  -> internalAxiom "IH" $ \(Forall xs' :: Forall nx [x]) (Forall ys' :: Forall ny [y]) a' -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs') (Forall ys') (a' :: Forall na a)
           CalcStrategy { calcIntros, calcProofSteps, calcResult } = mkCalcSteps $ steps ih x xs y ys a

       pure InductionStrategy {
                inductionIntros         = calcIntros
              , inductionBaseCase       = mkBaseCase style $ predicate SL.nil SL.nil a .&& predicate SL.nil (y SL..: ys) a .&& predicate (x SL..: xs) SL.nil a
              , inductionProofSteps     = calcProofSteps
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ", " ++ ny ++ ":" ++ nys ++ ")") (predicate (x SL..: xs) (y SL..: ys) a)
              , inductiveResult         = calcResult
              }

-- | Induction over two lists, simultaneously, taking two extra arguments
instance (KnownSymbol nx, SymVal x, KnownSymbol ny, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall ny [y] -> Forall na a -> Forall nb b -> SBool)
                   (SBV x -> SList x -> SBV y -> SList y -> SBV a -> SBV b -> (SBool, [ProofStep z]))
  where
   inductionStrategy style result steps = do
       let predicate xs ys a b = result (Forall xs) (Forall ys) (Forall a) (Forall b)
           nxs                 = symbolVal (Proxy @nx)
           nx                  = singular nxs
           nys                 = symbolVal (Proxy @ny)
           ny                  = singular nys
           na                  = symbolVal (Proxy @na)
           nb                  = symbolVal (Proxy @nb)

       x  <- free nx
       xs <- free nxs

       y  <- free ny
       ys <- free nys

       a  <- free na
       b  <- free nb

       let ih = case style of
                  RegularInduction -> internalAxiom "IH" $ \                                                            a' b' ->                                   result (Forall xs)  (Forall ys)  (a' :: Forall na a) (b' :: Forall nb b)
                  StrongInduction  -> internalAxiom "IH" $ \(Forall xs' :: Forall nx [x]) (Forall ys' :: Forall ny [y]) a' b' -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs') (Forall ys') (a' :: Forall na a) (b' :: Forall nb b)
           CalcStrategy { calcIntros, calcProofSteps, calcResult } = mkCalcSteps $ steps ih x xs y ys a b

       pure InductionStrategy {
                inductionIntros         = calcIntros
              , inductionBaseCase       = mkBaseCase style $ predicate SL.nil SL.nil a b .&& predicate SL.nil (y SL..: ys) a b .&& predicate (x SL..: xs) SL.nil a b
              , inductionProofSteps     = calcProofSteps
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ", " ++ ny ++ ":" ++ nys ++ ")") (predicate (x SL..: xs) (y SL..: ys) a b)
              , inductiveResult         = calcResult
              }

-- | Induction over two lists, simultaneously, taking three extra arguments
instance (KnownSymbol nx, SymVal x, KnownSymbol ny, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall ny [y] -> Forall na a -> Forall nb b -> Forall nc c -> SBool)
                   (SBV x -> SList x -> SBV y -> SList y -> SBV a -> SBV b -> SBV c -> (SBool, [ProofStep z]))
  where
   inductionStrategy style result steps = do
       let predicate xs ys a b c = result (Forall xs) (Forall ys) (Forall a) (Forall b) (Forall c)
           nxs                   = symbolVal (Proxy @nx)
           nx                    = singular nxs
           nys                   = symbolVal (Proxy @ny)
           ny                    = singular nys
           na                    = symbolVal (Proxy @na)
           nb                    = symbolVal (Proxy @nb)
           nc                    = symbolVal (Proxy @nc)

       x  <- free nx
       xs <- free nxs

       y  <- free ny
       ys <- free nys

       a  <- free na
       b  <- free nb
       c  <- free nc

       let ih = case style of
                  RegularInduction -> internalAxiom "IH" $ \                                                            a' b' c' ->                                   result (Forall xs)  (Forall ys)  (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c)
                  StrongInduction  -> internalAxiom "IH" $ \(Forall xs' :: Forall nx [x]) (Forall ys' :: Forall ny [y]) a' b' c' -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs') (Forall ys') (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c)
           CalcStrategy { calcIntros, calcProofSteps, calcResult } = mkCalcSteps $ steps ih x xs y ys a b c

       pure InductionStrategy {
                inductionIntros         = calcIntros
              , inductionBaseCase       = mkBaseCase style $ predicate SL.nil SL.nil a b c .&& predicate SL.nil (y SL..: ys) a b c .&& predicate (x SL..: xs) SL.nil a b c
              , inductionProofSteps     = calcProofSteps
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ", " ++ ny ++ ":" ++ nys ++ ")") (predicate (x SL..: xs) (y SL..: ys) a b c)
              , inductiveResult         = calcResult
              }

-- | Induction over two lists, simultaneously, taking four extra arguments
instance (KnownSymbol nx, SymVal x, KnownSymbol ny, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall ny [y] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                   (SBV x -> SList x -> SBV y -> SList y -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, [ProofStep z]))
  where
   inductionStrategy style result steps = do
       let predicate xs ys a b c d = result (Forall xs) (Forall ys) (Forall a) (Forall b) (Forall c) (Forall d)
           nxs                     = symbolVal (Proxy @nx)
           nx                      = singular nxs
           nys                     = symbolVal (Proxy @ny)
           ny                      = singular nys
           na                      = symbolVal (Proxy @na)
           nb                      = symbolVal (Proxy @nb)
           nc                      = symbolVal (Proxy @nc)
           nd                      = symbolVal (Proxy @nd)

       x  <- free nx
       xs <- free nxs

       y  <- free ny
       ys <- free nys

       a  <- free na
       b  <- free nb
       c  <- free nc
       d  <- free nd

       let ih = case style of
                  RegularInduction -> internalAxiom "IH" $ \                                                            a' b' c' d' ->                                   result (Forall xs)  (Forall ys)  (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c) (d' :: Forall nd d)
                  StrongInduction  -> internalAxiom "IH" $ \(Forall xs' :: Forall nx [x]) (Forall ys' :: Forall ny [y]) a' b' c' d' -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs') (Forall ys') (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c) (d' :: Forall nd d)
           CalcStrategy { calcIntros, calcProofSteps, calcResult } = mkCalcSteps $ steps ih x xs y ys a b c d

       pure InductionStrategy {
                inductionIntros         = calcIntros
              , inductionBaseCase       = mkBaseCase style $ predicate SL.nil SL.nil a b c d .&& predicate SL.nil (y SL..: ys) a b c d .&& predicate (x SL..: xs) SL.nil a b c d
              , inductionProofSteps     = calcProofSteps
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ", " ++ ny ++ ":" ++ nys ++ ")") (predicate (x SL..: xs) (y SL..: ys) a b c d)
              , inductiveResult         = calcResult
              }

-- | Induction over two lists, simultaneously, taking four extra arguments
instance (KnownSymbol nx, SymVal x, KnownSymbol ny, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z)
      => Inductive (Forall nx [x] -> Forall ny [y] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool)
                   (SBV x -> SList x -> SBV y -> SList y -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, [ProofStep z]))
  where
   inductionStrategy style result steps = do
       let predicate xs ys a b c d e = result (Forall xs) (Forall ys) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)
           nxs                       = symbolVal (Proxy @nx)
           nx                        = singular nxs
           nys                       = symbolVal (Proxy @ny)
           ny                        = singular nys
           na                        = symbolVal (Proxy @na)
           nb                        = symbolVal (Proxy @nb)
           nc                        = symbolVal (Proxy @nc)
           nd                        = symbolVal (Proxy @nd)
           ne                        = symbolVal (Proxy @ne)

       x  <- free nx
       xs <- free nxs

       y  <- free ny
       ys <- free nys

       a  <- free na
       b  <- free nb
       c  <- free nc
       d  <- free nd
       e  <- free ne

       let ih = case style of
                  RegularInduction -> internalAxiom "IH" $ \                                                            a' b' c' d' e' ->                                   result (Forall xs)  (Forall ys)  (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c) (d' :: Forall nd d) (e' :: Forall ne e)
                  StrongInduction  -> internalAxiom "IH" $ \(Forall xs' :: Forall nx [x]) (Forall ys' :: Forall ny [y]) a' b' c' d' e' -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs') (Forall ys') (a' :: Forall na a) (b' :: Forall nb b) (c' :: Forall nc c) (d' :: Forall nd d) (e' :: Forall ne e)
           CalcStrategy { calcIntros, calcProofSteps, calcResult } = mkCalcSteps $ steps ih x xs y ys a b c d e

       pure InductionStrategy {
                inductionIntros         = calcIntros
              , inductionBaseCase       = mkBaseCase style $ predicate SL.nil SL.nil a b c d e .&& predicate SL.nil (y SL..: ys) a b c d e .&& predicate (x SL..: xs) SL.nil a b c d e
              , inductionProofSteps     = calcProofSteps
              , inductiveStep           = observeIf not ("P(" ++ nx ++ ":" ++ nxs ++ ", " ++ ny ++ ":" ++ nys ++ ")") (predicate (x SL..: xs) (y SL..: ys) a b c d e)
              , inductiveResult         = calcResult
              }

-------------------------------------}

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

-- | Instantiate a proof over an arg. This uses dynamic typing, kind of hacky, but works sufficiently well.
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
               | not (any isSpace s)                      = s
               | True                                     = '(' : s ++ ")"

-- | Helpers for a step
data Helper = HelperProof Proof          -- A previously proven theorem
            | HelperAssum SBool          -- A hypothesis
            | HelperCase  String [SBool] -- Case split

-- | Get proofs from helpers
getHelperProofs :: [Helper] -> [Proof]
getHelperProofs = concatMap get
  where get (HelperProof p) = [p]
        get HelperAssum {}  = []
        get HelperCase  {}  = []

-- | Get proofs from helpers
getHelperAssumes :: [Helper] -> [SBool]
getHelperAssumes = concatMap get
  where get HelperProof  {} = []
        get (HelperAssum b) = [b]
        get HelperCase   {} = []

-- | Smart constructor for creating a helper from a boolean. This is hardly needed, unless you're
-- mixing proofs and booleans in one group of hints.
hyp :: SBool -> Helper
hyp = HelperAssum

-- | Smart constructor for creating a helper from a boolean. This is hardly needed, unless you're
-- mixing proofs and booleans in one group of hints.
hprf :: Proof -> Helper
hprf = HelperProof

-- | A proof-step with associated helpers
data ProofStep a = SingleStep a [Helper]

-- | Class capturing giving a proof-step helper
class ProofHint a b where
  -- | Specify a helper for the given proof step
  (??) :: a -> b -> ProofStep a
  infixl 2 ??

-- | Giving just one proof as a helper.
instance ProofHint a Proof where
  a ?? p = SingleStep a [HelperProof p]

-- | Giving just one boolean as a helper.
instance ProofHint a SBool where
  a ?? p = SingleStep a [HelperAssum p]

-- | Giving just one helper
instance ProofHint a Helper where
  a ?? h = SingleStep a [h]

-- | Giving a bunch of proofs as a helper.
instance ProofHint a [Proof] where
  a ?? ps = SingleStep a (map HelperProof ps)

-- | Giving a bunch of booleans as a helper.
instance ProofHint a [SBool] where
  a ?? ps = SingleStep a (map HelperAssum ps)

-- | Giving a set of helpers
instance ProofHint a [Helper] where
  a ?? hs = SingleStep a hs

-- | Giving user a hint as a string. This doesn't actually do anything for the solver, it just helps with readability
instance ProofHint a String where
  a ?? _ = SingleStep a []

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

-- | Unicode alternative for `=:`.
(≡) :: ChainStep a (ChainsTo a) =>  a -> ChainsTo a -> ChainsTo a
(≡) = (=:)
infixr 1 ≡

-- | Chaining two steps together
class ChainStep a b where
  chain :: a -> b -> b

-- | Chaining from a value without any annotation
instance ChainStep a [ProofStep a] where
  chain x y = SingleStep x [] : y

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

-- | Alternative unicode for `|-`.
(⊢) :: [SBool] -> [ProofStep a] -> (SBool, [ProofStep a])
(⊢) = (|-)
infixl 0 ⊢

-- | Alternative unicode for `??`.
(⁇) :: ProofHint a b => a -> b -> ProofStep a
(⁇) = (??)
infixl 2 ⁇

-- | Specifying a case-split
cases :: String -> [SBool] -> Helper
cases = HelperCase
